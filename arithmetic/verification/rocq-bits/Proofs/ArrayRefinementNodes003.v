(* Generated node equalities; not yet a whole-circuit refinement. *)
    From Stdlib Require Import ZArith Lia Zmod.Bits.
    From BitsProofs Require Export ArrayRefinementBase.
    From BitsProofs Require Import RefinementTactics.
    Open Scope Z_scope.

From BitsProofs Require Export ArrayRefinementNodes002.
Lemma node_3000 (s : N.State) (i : N.Inputs) :
  R.v3000 (state s) (inputs i) = Zmod.unsigned (N.v3000 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3000 s i)) at 1.
  unfold R.v3000, N.v3000.
  rewrite ?node_2999.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1243_nr_5F1243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1243_nr_5F1243 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3001 (s : N.State) (i : N.Inputs) :
  R.v3001 (state s) (inputs i) = Zmod.unsigned (N.v3001 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3001 s i)) at 1.
  unfold R.v3001, N.v3001.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3002 (s : N.State) (i : N.Inputs) :
  R.v3002 (state s) (inputs i) = Zmod.unsigned (N.v3002 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3002 s i)) at 1.
  unfold R.v3002, N.v3002.
  rewrite ?node_3001.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1244_nr_5F1244.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1244_nr_5F1244 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3003 (s : N.State) (i : N.Inputs) :
  R.v3003 (state s) (inputs i) = Zmod.unsigned (N.v3003 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3003 s i)) at 1.
  unfold R.v3003, N.v3003.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3004 (s : N.State) (i : N.Inputs) :
  R.v3004 (state s) (inputs i) = Zmod.unsigned (N.v3004 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3004 s i)) at 1.
  unfold R.v3004, N.v3004.
  rewrite ?node_3003.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1245_nr_5F1245.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1245_nr_5F1245 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3005 (s : N.State) (i : N.Inputs) :
  R.v3005 (state s) (inputs i) = Zmod.unsigned (N.v3005 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3005 s i)) at 1.
  unfold R.v3005, N.v3005.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3006 (s : N.State) (i : N.Inputs) :
  R.v3006 (state s) (inputs i) = Zmod.unsigned (N.v3006 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3006 s i)) at 1.
  unfold R.v3006, N.v3006.
  rewrite ?node_3005.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1246_nr_5F1246.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1246_nr_5F1246 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3007 (s : N.State) (i : N.Inputs) :
  R.v3007 (state s) (inputs i) = Zmod.unsigned (N.v3007 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3007 s i)) at 1.
  unfold R.v3007, N.v3007.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3008 (s : N.State) (i : N.Inputs) :
  R.v3008 (state s) (inputs i) = Zmod.unsigned (N.v3008 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3008 s i)) at 1.
  unfold R.v3008, N.v3008.
  rewrite ?node_3007.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1247_nr_5F1247.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1247_nr_5F1247 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3009 (s : N.State) (i : N.Inputs) :
  R.v3009 (state s) (inputs i) = Zmod.unsigned (N.v3009 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3009 s i)) at 1.
  unfold R.v3009, N.v3009.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3010 (s : N.State) (i : N.Inputs) :
  R.v3010 (state s) (inputs i) = Zmod.unsigned (N.v3010 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3010 s i)) at 1.
  unfold R.v3010, N.v3010.
  rewrite ?node_3009.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1248_nr_5F1248.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1248_nr_5F1248 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3011 (s : N.State) (i : N.Inputs) :
  R.v3011 (state s) (inputs i) = Zmod.unsigned (N.v3011 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3011 s i)) at 1.
  unfold R.v3011, N.v3011.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3012 (s : N.State) (i : N.Inputs) :
  R.v3012 (state s) (inputs i) = Zmod.unsigned (N.v3012 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3012 s i)) at 1.
  unfold R.v3012, N.v3012.
  rewrite ?node_3011.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1249_nr_5F1249.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1249_nr_5F1249 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3013 (s : N.State) (i : N.Inputs) :
  R.v3013 (state s) (inputs i) = Zmod.unsigned (N.v3013 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3013 s i)) at 1.
  unfold R.v3013, N.v3013.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3014 (s : N.State) (i : N.Inputs) :
  R.v3014 (state s) (inputs i) = Zmod.unsigned (N.v3014 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3014 s i)) at 1.
  unfold R.v3014, N.v3014.
  rewrite ?node_3013.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1250_nr_5F1250.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1250_nr_5F1250 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3015 (s : N.State) (i : N.Inputs) :
  R.v3015 (state s) (inputs i) = Zmod.unsigned (N.v3015 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3015 s i)) at 1.
  unfold R.v3015, N.v3015.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3016 (s : N.State) (i : N.Inputs) :
  R.v3016 (state s) (inputs i) = Zmod.unsigned (N.v3016 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3016 s i)) at 1.
  unfold R.v3016, N.v3016.
  rewrite ?node_3015.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1251_nr_5F1251.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1251_nr_5F1251 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3017 (s : N.State) (i : N.Inputs) :
  R.v3017 (state s) (inputs i) = Zmod.unsigned (N.v3017 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3017 s i)) at 1.
  unfold R.v3017, N.v3017.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3018 (s : N.State) (i : N.Inputs) :
  R.v3018 (state s) (inputs i) = Zmod.unsigned (N.v3018 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3018 s i)) at 1.
  unfold R.v3018, N.v3018.
  rewrite ?node_3017.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1252_nr_5F1252.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1252_nr_5F1252 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3019 (s : N.State) (i : N.Inputs) :
  R.v3019 (state s) (inputs i) = Zmod.unsigned (N.v3019 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3019 s i)) at 1.
  unfold R.v3019, N.v3019.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3020 (s : N.State) (i : N.Inputs) :
  R.v3020 (state s) (inputs i) = Zmod.unsigned (N.v3020 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3020 s i)) at 1.
  unfold R.v3020, N.v3020.
  rewrite ?node_3019.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1253_nr_5F1253.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1253_nr_5F1253 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3021 (s : N.State) (i : N.Inputs) :
  R.v3021 (state s) (inputs i) = Zmod.unsigned (N.v3021 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3021 s i)) at 1.
  unfold R.v3021, N.v3021.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3022 (s : N.State) (i : N.Inputs) :
  R.v3022 (state s) (inputs i) = Zmod.unsigned (N.v3022 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3022 s i)) at 1.
  unfold R.v3022, N.v3022.
  rewrite ?node_2890.
  unfold R.v3021, N.v3021.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3023 (s : N.State) (i : N.Inputs) :
  R.v3023 (state s) (inputs i) = Zmod.unsigned (N.v3023 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3023 s i)) at 1.
  unfold R.v3023, N.v3023.
  rewrite ?node_3022.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1254_nr_5F1254.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1254_nr_5F1254 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3024 (s : N.State) (i : N.Inputs) :
  R.v3024 (state s) (inputs i) = Zmod.unsigned (N.v3024 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3024 s i)) at 1.
  unfold R.v3024, N.v3024.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3025 (s : N.State) (i : N.Inputs) :
  R.v3025 (state s) (inputs i) = Zmod.unsigned (N.v3025 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3025 s i)) at 1.
  unfold R.v3025, N.v3025.
  unfold R.v3021, N.v3021.
  rewrite ?node_3024.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3026 (s : N.State) (i : N.Inputs) :
  R.v3026 (state s) (inputs i) = Zmod.unsigned (N.v3026 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3026 s i)) at 1.
  unfold R.v3026, N.v3026.
  rewrite ?node_3025.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1255_nr_5F1255.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1255_nr_5F1255 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3027 (s : N.State) (i : N.Inputs) :
  R.v3027 (state s) (inputs i) = Zmod.unsigned (N.v3027 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3027 s i)) at 1.
  unfold R.v3027, N.v3027.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3028 (s : N.State) (i : N.Inputs) :
  R.v3028 (state s) (inputs i) = Zmod.unsigned (N.v3028 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3028 s i)) at 1.
  unfold R.v3028, N.v3028.
  rewrite ?node_3027.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1256_nr_5F1256.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1256_nr_5F1256 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3029 (s : N.State) (i : N.Inputs) :
  R.v3029 (state s) (inputs i) = Zmod.unsigned (N.v3029 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3029 s i)) at 1.
  unfold R.v3029, N.v3029.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3030 (s : N.State) (i : N.Inputs) :
  R.v3030 (state s) (inputs i) = Zmod.unsigned (N.v3030 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3030 s i)) at 1.
  unfold R.v3030, N.v3030.
  rewrite ?node_3029.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1257_nr_5F1257.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1257_nr_5F1257 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3031 (s : N.State) (i : N.Inputs) :
  R.v3031 (state s) (inputs i) = Zmod.unsigned (N.v3031 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3031 s i)) at 1.
  unfold R.v3031, N.v3031.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3032 (s : N.State) (i : N.Inputs) :
  R.v3032 (state s) (inputs i) = Zmod.unsigned (N.v3032 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3032 s i)) at 1.
  unfold R.v3032, N.v3032.
  rewrite ?node_3031.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1258_nr_5F1258.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1258_nr_5F1258 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3033 (s : N.State) (i : N.Inputs) :
  R.v3033 (state s) (inputs i) = Zmod.unsigned (N.v3033 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3033 s i)) at 1.
  unfold R.v3033, N.v3033.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3034 (s : N.State) (i : N.Inputs) :
  R.v3034 (state s) (inputs i) = Zmod.unsigned (N.v3034 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3034 s i)) at 1.
  unfold R.v3034, N.v3034.
  rewrite ?node_3033.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1259_nr_5F1259.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1259_nr_5F1259 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3035 (s : N.State) (i : N.Inputs) :
  R.v3035 (state s) (inputs i) = Zmod.unsigned (N.v3035 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3035 s i)) at 1.
  unfold R.v3035, N.v3035.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3036 (s : N.State) (i : N.Inputs) :
  R.v3036 (state s) (inputs i) = Zmod.unsigned (N.v3036 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3036 s i)) at 1.
  unfold R.v3036, N.v3036.
  rewrite ?node_3035.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1260_nr_5F1260.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1260_nr_5F1260 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3037 (s : N.State) (i : N.Inputs) :
  R.v3037 (state s) (inputs i) = Zmod.unsigned (N.v3037 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3037 s i)) at 1.
  unfold R.v3037, N.v3037.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3038 (s : N.State) (i : N.Inputs) :
  R.v3038 (state s) (inputs i) = Zmod.unsigned (N.v3038 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3038 s i)) at 1.
  unfold R.v3038, N.v3038.
  rewrite ?node_3037.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1261_nr_5F1261.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1261_nr_5F1261 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3039 (s : N.State) (i : N.Inputs) :
  R.v3039 (state s) (inputs i) = Zmod.unsigned (N.v3039 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3039 s i)) at 1.
  unfold R.v3039, N.v3039.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3040 (s : N.State) (i : N.Inputs) :
  R.v3040 (state s) (inputs i) = Zmod.unsigned (N.v3040 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3040 s i)) at 1.
  unfold R.v3040, N.v3040.
  rewrite ?node_3039.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1262_nr_5F1262.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1262_nr_5F1262 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3041 (s : N.State) (i : N.Inputs) :
  R.v3041 (state s) (inputs i) = Zmod.unsigned (N.v3041 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3041 s i)) at 1.
  unfold R.v3041, N.v3041.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3042 (s : N.State) (i : N.Inputs) :
  R.v3042 (state s) (inputs i) = Zmod.unsigned (N.v3042 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3042 s i)) at 1.
  unfold R.v3042, N.v3042.
  rewrite ?node_3041.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1263_nr_5F1263.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1263_nr_5F1263 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3043 (s : N.State) (i : N.Inputs) :
  R.v3043 (state s) (inputs i) = Zmod.unsigned (N.v3043 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3043 s i)) at 1.
  unfold R.v3043, N.v3043.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3044 (s : N.State) (i : N.Inputs) :
  R.v3044 (state s) (inputs i) = Zmod.unsigned (N.v3044 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3044 s i)) at 1.
  unfold R.v3044, N.v3044.
  rewrite ?node_3043.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1264_nr_5F1264.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1264_nr_5F1264 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3045 (s : N.State) (i : N.Inputs) :
  R.v3045 (state s) (inputs i) = Zmod.unsigned (N.v3045 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3045 s i)) at 1.
  unfold R.v3045, N.v3045.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3046 (s : N.State) (i : N.Inputs) :
  R.v3046 (state s) (inputs i) = Zmod.unsigned (N.v3046 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3046 s i)) at 1.
  unfold R.v3046, N.v3046.
  rewrite ?node_3045.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1265_nr_5F1265.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1265_nr_5F1265 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3047 (s : N.State) (i : N.Inputs) :
  R.v3047 (state s) (inputs i) = Zmod.unsigned (N.v3047 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3047 s i)) at 1.
  unfold R.v3047, N.v3047.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3048 (s : N.State) (i : N.Inputs) :
  R.v3048 (state s) (inputs i) = Zmod.unsigned (N.v3048 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3048 s i)) at 1.
  unfold R.v3048, N.v3048.
  rewrite ?node_3047.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1266_nr_5F1266.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1266_nr_5F1266 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3049 (s : N.State) (i : N.Inputs) :
  R.v3049 (state s) (inputs i) = Zmod.unsigned (N.v3049 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3049 s i)) at 1.
  unfold R.v3049, N.v3049.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3050 (s : N.State) (i : N.Inputs) :
  R.v3050 (state s) (inputs i) = Zmod.unsigned (N.v3050 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3050 s i)) at 1.
  unfold R.v3050, N.v3050.
  rewrite ?node_3049.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1267_nr_5F1267.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1267_nr_5F1267 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3051 (s : N.State) (i : N.Inputs) :
  R.v3051 (state s) (inputs i) = Zmod.unsigned (N.v3051 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3051 s i)) at 1.
  unfold R.v3051, N.v3051.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3052 (s : N.State) (i : N.Inputs) :
  R.v3052 (state s) (inputs i) = Zmod.unsigned (N.v3052 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3052 s i)) at 1.
  unfold R.v3052, N.v3052.
  rewrite ?node_3051.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1268_nr_5F1268.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1268_nr_5F1268 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3053 (s : N.State) (i : N.Inputs) :
  R.v3053 (state s) (inputs i) = Zmod.unsigned (N.v3053 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3053 s i)) at 1.
  unfold R.v3053, N.v3053.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3054 (s : N.State) (i : N.Inputs) :
  R.v3054 (state s) (inputs i) = Zmod.unsigned (N.v3054 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3054 s i)) at 1.
  unfold R.v3054, N.v3054.
  rewrite ?node_3053.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1269_nr_5F1269.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1269_nr_5F1269 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3055 (s : N.State) (i : N.Inputs) :
  R.v3055 (state s) (inputs i) = Zmod.unsigned (N.v3055 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3055 s i)) at 1.
  unfold R.v3055, N.v3055.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3056 (s : N.State) (i : N.Inputs) :
  R.v3056 (state s) (inputs i) = Zmod.unsigned (N.v3056 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3056 s i)) at 1.
  unfold R.v3056, N.v3056.
  rewrite ?node_3055.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1270_nr_5F1270.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1270_nr_5F1270 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3057 (s : N.State) (i : N.Inputs) :
  R.v3057 (state s) (inputs i) = Zmod.unsigned (N.v3057 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3057 s i)) at 1.
  unfold R.v3057, N.v3057.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3058 (s : N.State) (i : N.Inputs) :
  R.v3058 (state s) (inputs i) = Zmod.unsigned (N.v3058 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3058 s i)) at 1.
  unfold R.v3058, N.v3058.
  rewrite ?node_3057.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1271_nr_5F1271.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1271_nr_5F1271 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3059 (s : N.State) (i : N.Inputs) :
  R.v3059 (state s) (inputs i) = Zmod.unsigned (N.v3059 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3059 s i)) at 1.
  unfold R.v3059, N.v3059.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3060 (s : N.State) (i : N.Inputs) :
  R.v3060 (state s) (inputs i) = Zmod.unsigned (N.v3060 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3060 s i)) at 1.
  unfold R.v3060, N.v3060.
  rewrite ?node_3059.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1272_nr_5F1272.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1272_nr_5F1272 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3061 (s : N.State) (i : N.Inputs) :
  R.v3061 (state s) (inputs i) = Zmod.unsigned (N.v3061 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3061 s i)) at 1.
  unfold R.v3061, N.v3061.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3062 (s : N.State) (i : N.Inputs) :
  R.v3062 (state s) (inputs i) = Zmod.unsigned (N.v3062 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3062 s i)) at 1.
  unfold R.v3062, N.v3062.
  rewrite ?node_3061.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1273_nr_5F1273.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1273_nr_5F1273 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3063 (s : N.State) (i : N.Inputs) :
  R.v3063 (state s) (inputs i) = Zmod.unsigned (N.v3063 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3063 s i)) at 1.
  unfold R.v3063, N.v3063.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3064 (s : N.State) (i : N.Inputs) :
  R.v3064 (state s) (inputs i) = Zmod.unsigned (N.v3064 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3064 s i)) at 1.
  unfold R.v3064, N.v3064.
  rewrite ?node_3063.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1274_nr_5F1274.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1274_nr_5F1274 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3065 (s : N.State) (i : N.Inputs) :
  R.v3065 (state s) (inputs i) = Zmod.unsigned (N.v3065 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3065 s i)) at 1.
  unfold R.v3065, N.v3065.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3066 (s : N.State) (i : N.Inputs) :
  R.v3066 (state s) (inputs i) = Zmod.unsigned (N.v3066 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3066 s i)) at 1.
  unfold R.v3066, N.v3066.
  rewrite ?node_3065.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1275_nr_5F1275.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1275_nr_5F1275 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3067 (s : N.State) (i : N.Inputs) :
  R.v3067 (state s) (inputs i) = Zmod.unsigned (N.v3067 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3067 s i)) at 1.
  unfold R.v3067, N.v3067.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3068 (s : N.State) (i : N.Inputs) :
  R.v3068 (state s) (inputs i) = Zmod.unsigned (N.v3068 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3068 s i)) at 1.
  unfold R.v3068, N.v3068.
  rewrite ?node_3067.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1276_nr_5F1276.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1276_nr_5F1276 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3069 (s : N.State) (i : N.Inputs) :
  R.v3069 (state s) (inputs i) = Zmod.unsigned (N.v3069 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3069 s i)) at 1.
  unfold R.v3069, N.v3069.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3070 (s : N.State) (i : N.Inputs) :
  R.v3070 (state s) (inputs i) = Zmod.unsigned (N.v3070 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3070 s i)) at 1.
  unfold R.v3070, N.v3070.
  rewrite ?node_3069.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1277_nr_5F1277.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1277_nr_5F1277 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3071 (s : N.State) (i : N.Inputs) :
  R.v3071 (state s) (inputs i) = Zmod.unsigned (N.v3071 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3071 s i)) at 1.
  unfold R.v3071, N.v3071.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3072 (s : N.State) (i : N.Inputs) :
  R.v3072 (state s) (inputs i) = Zmod.unsigned (N.v3072 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3072 s i)) at 1.
  unfold R.v3072, N.v3072.
  rewrite ?node_3071.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1278_nr_5F1278.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1278_nr_5F1278 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3073 (s : N.State) (i : N.Inputs) :
  R.v3073 (state s) (inputs i) = Zmod.unsigned (N.v3073 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3073 s i)) at 1.
  unfold R.v3073, N.v3073.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3074 (s : N.State) (i : N.Inputs) :
  R.v3074 (state s) (inputs i) = Zmod.unsigned (N.v3074 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3074 s i)) at 1.
  unfold R.v3074, N.v3074.
  rewrite ?node_3073.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1279_nr_5F1279.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1279_nr_5F1279 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3075 (s : N.State) (i : N.Inputs) :
  R.v3075 (state s) (inputs i) = Zmod.unsigned (N.v3075 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3075 s i)) at 1.
  unfold R.v3075, N.v3075.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3076 (s : N.State) (i : N.Inputs) :
  R.v3076 (state s) (inputs i) = Zmod.unsigned (N.v3076 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3076 s i)) at 1.
  unfold R.v3076, N.v3076.
  rewrite ?node_3075.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1280_nr_5F1280.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1280_nr_5F1280 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3077 (s : N.State) (i : N.Inputs) :
  R.v3077 (state s) (inputs i) = Zmod.unsigned (N.v3077 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3077 s i)) at 1.
  unfold R.v3077, N.v3077.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3078 (s : N.State) (i : N.Inputs) :
  R.v3078 (state s) (inputs i) = Zmod.unsigned (N.v3078 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3078 s i)) at 1.
  unfold R.v3078, N.v3078.
  rewrite ?node_3077.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1281_nr_5F1281.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1281_nr_5F1281 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3079 (s : N.State) (i : N.Inputs) :
  R.v3079 (state s) (inputs i) = Zmod.unsigned (N.v3079 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3079 s i)) at 1.
  unfold R.v3079, N.v3079.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3080 (s : N.State) (i : N.Inputs) :
  R.v3080 (state s) (inputs i) = Zmod.unsigned (N.v3080 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3080 s i)) at 1.
  unfold R.v3080, N.v3080.
  rewrite ?node_3079.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1282_nr_5F1282.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1282_nr_5F1282 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3081 (s : N.State) (i : N.Inputs) :
  R.v3081 (state s) (inputs i) = Zmod.unsigned (N.v3081 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3081 s i)) at 1.
  unfold R.v3081, N.v3081.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3082 (s : N.State) (i : N.Inputs) :
  R.v3082 (state s) (inputs i) = Zmod.unsigned (N.v3082 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3082 s i)) at 1.
  unfold R.v3082, N.v3082.
  rewrite ?node_3081.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1283_nr_5F1283.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1283_nr_5F1283 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3083 (s : N.State) (i : N.Inputs) :
  R.v3083 (state s) (inputs i) = Zmod.unsigned (N.v3083 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3083 s i)) at 1.
  unfold R.v3083, N.v3083.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3084 (s : N.State) (i : N.Inputs) :
  R.v3084 (state s) (inputs i) = Zmod.unsigned (N.v3084 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3084 s i)) at 1.
  unfold R.v3084, N.v3084.
  rewrite ?node_3083.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1284_nr_5F1284.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1284_nr_5F1284 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3085 (s : N.State) (i : N.Inputs) :
  R.v3085 (state s) (inputs i) = Zmod.unsigned (N.v3085 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3085 s i)) at 1.
  unfold R.v3085, N.v3085.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3086 (s : N.State) (i : N.Inputs) :
  R.v3086 (state s) (inputs i) = Zmod.unsigned (N.v3086 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3086 s i)) at 1.
  unfold R.v3086, N.v3086.
  rewrite ?node_3085.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1285_nr_5F1285.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1285_nr_5F1285 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3087 (s : N.State) (i : N.Inputs) :
  R.v3087 (state s) (inputs i) = Zmod.unsigned (N.v3087 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3087 s i)) at 1.
  unfold R.v3087, N.v3087.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3088 (s : N.State) (i : N.Inputs) :
  R.v3088 (state s) (inputs i) = Zmod.unsigned (N.v3088 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3088 s i)) at 1.
  unfold R.v3088, N.v3088.
  rewrite ?node_3087.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1286_nr_5F1286.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1286_nr_5F1286 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3089 (s : N.State) (i : N.Inputs) :
  R.v3089 (state s) (inputs i) = Zmod.unsigned (N.v3089 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3089 s i)) at 1.
  unfold R.v3089, N.v3089.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3090 (s : N.State) (i : N.Inputs) :
  R.v3090 (state s) (inputs i) = Zmod.unsigned (N.v3090 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3090 s i)) at 1.
  unfold R.v3090, N.v3090.
  rewrite ?node_3089.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1287_nr_5F1288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1287_nr_5F1288 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3091 (s : N.State) (i : N.Inputs) :
  R.v3091 (state s) (inputs i) = Zmod.unsigned (N.v3091 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3091 s i)) at 1.
  unfold R.v3091, N.v3091.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3092 (s : N.State) (i : N.Inputs) :
  R.v3092 (state s) (inputs i) = Zmod.unsigned (N.v3092 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3092 s i)) at 1.
  unfold R.v3092, N.v3092.
  rewrite ?node_3091.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1288_nr_5F1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1288_nr_5F1289 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3093 (s : N.State) (i : N.Inputs) :
  R.v3093 (state s) (inputs i) = Zmod.unsigned (N.v3093 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3093 s i)) at 1.
  unfold R.v3093, N.v3093.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3094 (s : N.State) (i : N.Inputs) :
  R.v3094 (state s) (inputs i) = Zmod.unsigned (N.v3094 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3094 s i)) at 1.
  unfold R.v3094, N.v3094.
  rewrite ?node_3093.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1289_nr_5F1290.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1289_nr_5F1290 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3095 (s : N.State) (i : N.Inputs) :
  R.v3095 (state s) (inputs i) = Zmod.unsigned (N.v3095 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3095 s i)) at 1.
  unfold R.v3095, N.v3095.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3096 (s : N.State) (i : N.Inputs) :
  R.v3096 (state s) (inputs i) = Zmod.unsigned (N.v3096 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3096 s i)) at 1.
  unfold R.v3096, N.v3096.
  rewrite ?node_3095.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1290_nr_5F1291.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1290_nr_5F1291 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3097 (s : N.State) (i : N.Inputs) :
  R.v3097 (state s) (inputs i) = Zmod.unsigned (N.v3097 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3097 s i)) at 1.
  unfold R.v3097, N.v3097.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3098 (s : N.State) (i : N.Inputs) :
  R.v3098 (state s) (inputs i) = Zmod.unsigned (N.v3098 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3098 s i)) at 1.
  unfold R.v3098, N.v3098.
  rewrite ?node_3097.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1291_nr_5F1292.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1291_nr_5F1292 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3099 (s : N.State) (i : N.Inputs) :
  R.v3099 (state s) (inputs i) = Zmod.unsigned (N.v3099 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3099 s i)) at 1.
  unfold R.v3099, N.v3099.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3100 (s : N.State) (i : N.Inputs) :
  R.v3100 (state s) (inputs i) = Zmod.unsigned (N.v3100 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3100 s i)) at 1.
  unfold R.v3100, N.v3100.
  rewrite ?node_3099.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1292_nr_5F1293.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1292_nr_5F1293 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3101 (s : N.State) (i : N.Inputs) :
  R.v3101 (state s) (inputs i) = Zmod.unsigned (N.v3101 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3101 s i)) at 1.
  unfold R.v3101, N.v3101.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3102 (s : N.State) (i : N.Inputs) :
  R.v3102 (state s) (inputs i) = Zmod.unsigned (N.v3102 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3102 s i)) at 1.
  unfold R.v3102, N.v3102.
  rewrite ?node_3101.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1293_nr_5F1294.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1293_nr_5F1294 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3103 (s : N.State) (i : N.Inputs) :
  R.v3103 (state s) (inputs i) = Zmod.unsigned (N.v3103 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3103 s i)) at 1.
  unfold R.v3103, N.v3103.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3104 (s : N.State) (i : N.Inputs) :
  R.v3104 (state s) (inputs i) = Zmod.unsigned (N.v3104 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3104 s i)) at 1.
  unfold R.v3104, N.v3104.
  rewrite ?node_3103.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1294_nr_5F1295.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1294_nr_5F1295 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3105 (s : N.State) (i : N.Inputs) :
  R.v3105 (state s) (inputs i) = Zmod.unsigned (N.v3105 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3105 s i)) at 1.
  unfold R.v3105, N.v3105.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3106 (s : N.State) (i : N.Inputs) :
  R.v3106 (state s) (inputs i) = Zmod.unsigned (N.v3106 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3106 s i)) at 1.
  unfold R.v3106, N.v3106.
  rewrite ?node_3105.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1295_nr_5F1296.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1295_nr_5F1296 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3107 (s : N.State) (i : N.Inputs) :
  R.v3107 (state s) (inputs i) = Zmod.unsigned (N.v3107 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3107 s i)) at 1.
  unfold R.v3107, N.v3107.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3108 (s : N.State) (i : N.Inputs) :
  R.v3108 (state s) (inputs i) = Zmod.unsigned (N.v3108 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3108 s i)) at 1.
  unfold R.v3108, N.v3108.
  rewrite ?node_3107.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1296_nr_5F1297.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1296_nr_5F1297 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3109 (s : N.State) (i : N.Inputs) :
  R.v3109 (state s) (inputs i) = Zmod.unsigned (N.v3109 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3109 s i)) at 1.
  unfold R.v3109, N.v3109.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3110 (s : N.State) (i : N.Inputs) :
  R.v3110 (state s) (inputs i) = Zmod.unsigned (N.v3110 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3110 s i)) at 1.
  unfold R.v3110, N.v3110.
  rewrite ?node_3109.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1297_nr_5F1298.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1297_nr_5F1298 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3111 (s : N.State) (i : N.Inputs) :
  R.v3111 (state s) (inputs i) = Zmod.unsigned (N.v3111 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3111 s i)) at 1.
  unfold R.v3111, N.v3111.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3112 (s : N.State) (i : N.Inputs) :
  R.v3112 (state s) (inputs i) = Zmod.unsigned (N.v3112 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3112 s i)) at 1.
  unfold R.v3112, N.v3112.
  rewrite ?node_3111.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1298_nr_5F1299.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1298_nr_5F1299 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3113 (s : N.State) (i : N.Inputs) :
  R.v3113 (state s) (inputs i) = Zmod.unsigned (N.v3113 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3113 s i)) at 1.
  unfold R.v3113, N.v3113.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3114 (s : N.State) (i : N.Inputs) :
  R.v3114 (state s) (inputs i) = Zmod.unsigned (N.v3114 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3114 s i)) at 1.
  unfold R.v3114, N.v3114.
  rewrite ?node_3113.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1299_nr_5F1300.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1299_nr_5F1300 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3115 (s : N.State) (i : N.Inputs) :
  R.v3115 (state s) (inputs i) = Zmod.unsigned (N.v3115 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3115 s i)) at 1.
  unfold R.v3115, N.v3115.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3116 (s : N.State) (i : N.Inputs) :
  R.v3116 (state s) (inputs i) = Zmod.unsigned (N.v3116 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3116 s i)) at 1.
  unfold R.v3116, N.v3116.
  rewrite ?node_3115.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1300_nr_5F1301.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1300_nr_5F1301 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3117 (s : N.State) (i : N.Inputs) :
  R.v3117 (state s) (inputs i) = Zmod.unsigned (N.v3117 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3117 s i)) at 1.
  unfold R.v3117, N.v3117.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3118 (s : N.State) (i : N.Inputs) :
  R.v3118 (state s) (inputs i) = Zmod.unsigned (N.v3118 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3118 s i)) at 1.
  unfold R.v3118, N.v3118.
  rewrite ?node_3117.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1301_nr_5F1302.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1301_nr_5F1302 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3119 (s : N.State) (i : N.Inputs) :
  R.v3119 (state s) (inputs i) = Zmod.unsigned (N.v3119 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3119 s i)) at 1.
  unfold R.v3119, N.v3119.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3120 (s : N.State) (i : N.Inputs) :
  R.v3120 (state s) (inputs i) = Zmod.unsigned (N.v3120 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3120 s i)) at 1.
  unfold R.v3120, N.v3120.
  rewrite ?node_3119.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1302_nr_5F1303.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1302_nr_5F1303 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3121 (s : N.State) (i : N.Inputs) :
  R.v3121 (state s) (inputs i) = Zmod.unsigned (N.v3121 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3121 s i)) at 1.
  unfold R.v3121, N.v3121.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3122 (s : N.State) (i : N.Inputs) :
  R.v3122 (state s) (inputs i) = Zmod.unsigned (N.v3122 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3122 s i)) at 1.
  unfold R.v3122, N.v3122.
  rewrite ?node_3121.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1303_nr_5F1304.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1303_nr_5F1304 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3123 (s : N.State) (i : N.Inputs) :
  R.v3123 (state s) (inputs i) = Zmod.unsigned (N.v3123 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3123 s i)) at 1.
  unfold R.v3123, N.v3123.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3124 (s : N.State) (i : N.Inputs) :
  R.v3124 (state s) (inputs i) = Zmod.unsigned (N.v3124 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3124 s i)) at 1.
  unfold R.v3124, N.v3124.
  rewrite ?node_3123.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1304_nr_5F1305.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1304_nr_5F1305 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3125 (s : N.State) (i : N.Inputs) :
  R.v3125 (state s) (inputs i) = Zmod.unsigned (N.v3125 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3125 s i)) at 1.
  unfold R.v3125, N.v3125.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3126 (s : N.State) (i : N.Inputs) :
  R.v3126 (state s) (inputs i) = Zmod.unsigned (N.v3126 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3126 s i)) at 1.
  unfold R.v3126, N.v3126.
  rewrite ?node_3125.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1305_nr_5F1306.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1305_nr_5F1306 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3127 (s : N.State) (i : N.Inputs) :
  R.v3127 (state s) (inputs i) = Zmod.unsigned (N.v3127 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3127 s i)) at 1.
  unfold R.v3127, N.v3127.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3128 (s : N.State) (i : N.Inputs) :
  R.v3128 (state s) (inputs i) = Zmod.unsigned (N.v3128 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3128 s i)) at 1.
  unfold R.v3128, N.v3128.
  rewrite ?node_3127.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1306_nr_5F1307.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1306_nr_5F1307 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3129 (s : N.State) (i : N.Inputs) :
  R.v3129 (state s) (inputs i) = Zmod.unsigned (N.v3129 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3129 s i)) at 1.
  unfold R.v3129, N.v3129.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3130 (s : N.State) (i : N.Inputs) :
  R.v3130 (state s) (inputs i) = Zmod.unsigned (N.v3130 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3130 s i)) at 1.
  unfold R.v3130, N.v3130.
  rewrite ?node_3129.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1307_nr_5F1308.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1307_nr_5F1308 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3131 (s : N.State) (i : N.Inputs) :
  R.v3131 (state s) (inputs i) = Zmod.unsigned (N.v3131 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3131 s i)) at 1.
  unfold R.v3131, N.v3131.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3132 (s : N.State) (i : N.Inputs) :
  R.v3132 (state s) (inputs i) = Zmod.unsigned (N.v3132 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3132 s i)) at 1.
  unfold R.v3132, N.v3132.
  rewrite ?node_3131.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1308_nr_5F1309.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1308_nr_5F1309 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3133 (s : N.State) (i : N.Inputs) :
  R.v3133 (state s) (inputs i) = Zmod.unsigned (N.v3133 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3133 s i)) at 1.
  unfold R.v3133, N.v3133.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3134 (s : N.State) (i : N.Inputs) :
  R.v3134 (state s) (inputs i) = Zmod.unsigned (N.v3134 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3134 s i)) at 1.
  unfold R.v3134, N.v3134.
  rewrite ?node_3133.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1309_nr_5F1310.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1309_nr_5F1310 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3135 (s : N.State) (i : N.Inputs) :
  R.v3135 (state s) (inputs i) = Zmod.unsigned (N.v3135 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3135 s i)) at 1.
  unfold R.v3135, N.v3135.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3136 (s : N.State) (i : N.Inputs) :
  R.v3136 (state s) (inputs i) = Zmod.unsigned (N.v3136 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3136 s i)) at 1.
  unfold R.v3136, N.v3136.
  rewrite ?node_3135.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1310_nr_5F1311.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1310_nr_5F1311 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3137 (s : N.State) (i : N.Inputs) :
  R.v3137 (state s) (inputs i) = Zmod.unsigned (N.v3137 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3137 s i)) at 1.
  unfold R.v3137, N.v3137.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3138 (s : N.State) (i : N.Inputs) :
  R.v3138 (state s) (inputs i) = Zmod.unsigned (N.v3138 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3138 s i)) at 1.
  unfold R.v3138, N.v3138.
  rewrite ?node_3137.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1311_nr_5F1312.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1311_nr_5F1312 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3139 (s : N.State) (i : N.Inputs) :
  R.v3139 (state s) (inputs i) = Zmod.unsigned (N.v3139 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3139 s i)) at 1.
  unfold R.v3139, N.v3139.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3140 (s : N.State) (i : N.Inputs) :
  R.v3140 (state s) (inputs i) = Zmod.unsigned (N.v3140 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3140 s i)) at 1.
  unfold R.v3140, N.v3140.
  rewrite ?node_3139.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1312_nr_5F1313.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1312_nr_5F1313 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3141 (s : N.State) (i : N.Inputs) :
  R.v3141 (state s) (inputs i) = Zmod.unsigned (N.v3141 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3141 s i)) at 1.
  unfold R.v3141, N.v3141.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3142 (s : N.State) (i : N.Inputs) :
  R.v3142 (state s) (inputs i) = Zmod.unsigned (N.v3142 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3142 s i)) at 1.
  unfold R.v3142, N.v3142.
  rewrite ?node_3141.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1313_nr_5F1314.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1313_nr_5F1314 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3143 (s : N.State) (i : N.Inputs) :
  R.v3143 (state s) (inputs i) = Zmod.unsigned (N.v3143 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3143 s i)) at 1.
  unfold R.v3143, N.v3143.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3144 (s : N.State) (i : N.Inputs) :
  R.v3144 (state s) (inputs i) = Zmod.unsigned (N.v3144 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3144 s i)) at 1.
  unfold R.v3144, N.v3144.
  rewrite ?node_3143.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1314_nr_5F1315.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1314_nr_5F1315 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3145 (s : N.State) (i : N.Inputs) :
  R.v3145 (state s) (inputs i) = Zmod.unsigned (N.v3145 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3145 s i)) at 1.
  unfold R.v3145, N.v3145.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3146 (s : N.State) (i : N.Inputs) :
  R.v3146 (state s) (inputs i) = Zmod.unsigned (N.v3146 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3146 s i)) at 1.
  unfold R.v3146, N.v3146.
  rewrite ?node_3145.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1315_nr_5F1316.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1315_nr_5F1316 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3147 (s : N.State) (i : N.Inputs) :
  R.v3147 (state s) (inputs i) = Zmod.unsigned (N.v3147 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3147 s i)) at 1.
  unfold R.v3147, N.v3147.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3148 (s : N.State) (i : N.Inputs) :
  R.v3148 (state s) (inputs i) = Zmod.unsigned (N.v3148 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3148 s i)) at 1.
  unfold R.v3148, N.v3148.
  rewrite ?node_3147.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1316_nr_5F1317.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1316_nr_5F1317 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3149 (s : N.State) (i : N.Inputs) :
  R.v3149 (state s) (inputs i) = Zmod.unsigned (N.v3149 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3149 s i)) at 1.
  unfold R.v3149, N.v3149.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3150 (s : N.State) (i : N.Inputs) :
  R.v3150 (state s) (inputs i) = Zmod.unsigned (N.v3150 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3150 s i)) at 1.
  unfold R.v3150, N.v3150.
  rewrite ?node_3149.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1317_nr_5F1318.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1317_nr_5F1318 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3151 (s : N.State) (i : N.Inputs) :
  R.v3151 (state s) (inputs i) = Zmod.unsigned (N.v3151 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3151 s i)) at 1.
  unfold R.v3151, N.v3151.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3152 (s : N.State) (i : N.Inputs) :
  R.v3152 (state s) (inputs i) = Zmod.unsigned (N.v3152 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3152 s i)) at 1.
  unfold R.v3152, N.v3152.
  unfold R.v3021, N.v3021.
  rewrite ?node_3151.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3153 (s : N.State) (i : N.Inputs) :
  R.v3153 (state s) (inputs i) = Zmod.unsigned (N.v3153 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3153 s i)) at 1.
  unfold R.v3153, N.v3153.
  rewrite ?node_3152.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1318_nr_5F1319.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1318_nr_5F1319 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3154 (s : N.State) (i : N.Inputs) :
  R.v3154 (state s) (inputs i) = Zmod.unsigned (N.v3154 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3154 s i)) at 1.
  unfold R.v3154, N.v3154.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3155 (s : N.State) (i : N.Inputs) :
  R.v3155 (state s) (inputs i) = Zmod.unsigned (N.v3155 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3155 s i)) at 1.
  unfold R.v3155, N.v3155.
  rewrite ?node_3154.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1319_nr_5F1320.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1319_nr_5F1320 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3156 (s : N.State) (i : N.Inputs) :
  R.v3156 (state s) (inputs i) = Zmod.unsigned (N.v3156 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3156 s i)) at 1.
  unfold R.v3156, N.v3156.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3157 (s : N.State) (i : N.Inputs) :
  R.v3157 (state s) (inputs i) = Zmod.unsigned (N.v3157 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3157 s i)) at 1.
  unfold R.v3157, N.v3157.
  rewrite ?node_3156.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1320_nr_5F1321.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1320_nr_5F1321 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3158 (s : N.State) (i : N.Inputs) :
  R.v3158 (state s) (inputs i) = Zmod.unsigned (N.v3158 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3158 s i)) at 1.
  unfold R.v3158, N.v3158.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3159 (s : N.State) (i : N.Inputs) :
  R.v3159 (state s) (inputs i) = Zmod.unsigned (N.v3159 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3159 s i)) at 1.
  unfold R.v3159, N.v3159.
  rewrite ?node_3158.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1321_nr_5F1322.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1321_nr_5F1322 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3160 (s : N.State) (i : N.Inputs) :
  R.v3160 (state s) (inputs i) = Zmod.unsigned (N.v3160 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3160 s i)) at 1.
  unfold R.v3160, N.v3160.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3161 (s : N.State) (i : N.Inputs) :
  R.v3161 (state s) (inputs i) = Zmod.unsigned (N.v3161 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3161 s i)) at 1.
  unfold R.v3161, N.v3161.
  rewrite ?node_3160.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1322_nr_5F1323.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1322_nr_5F1323 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3162 (s : N.State) (i : N.Inputs) :
  R.v3162 (state s) (inputs i) = Zmod.unsigned (N.v3162 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3162 s i)) at 1.
  unfold R.v3162, N.v3162.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3163 (s : N.State) (i : N.Inputs) :
  R.v3163 (state s) (inputs i) = Zmod.unsigned (N.v3163 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3163 s i)) at 1.
  unfold R.v3163, N.v3163.
  rewrite ?node_3162.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1323_nr_5F1324.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1323_nr_5F1324 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3164 (s : N.State) (i : N.Inputs) :
  R.v3164 (state s) (inputs i) = Zmod.unsigned (N.v3164 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3164 s i)) at 1.
  unfold R.v3164, N.v3164.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3165 (s : N.State) (i : N.Inputs) :
  R.v3165 (state s) (inputs i) = Zmod.unsigned (N.v3165 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3165 s i)) at 1.
  unfold R.v3165, N.v3165.
  rewrite ?node_3164.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1324_nr_5F1325.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1324_nr_5F1325 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3166 (s : N.State) (i : N.Inputs) :
  R.v3166 (state s) (inputs i) = Zmod.unsigned (N.v3166 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3166 s i)) at 1.
  unfold R.v3166, N.v3166.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3167 (s : N.State) (i : N.Inputs) :
  R.v3167 (state s) (inputs i) = Zmod.unsigned (N.v3167 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3167 s i)) at 1.
  unfold R.v3167, N.v3167.
  rewrite ?node_3166.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1325_nr_5F1326.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1325_nr_5F1326 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3168 (s : N.State) (i : N.Inputs) :
  R.v3168 (state s) (inputs i) = Zmod.unsigned (N.v3168 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3168 s i)) at 1.
  unfold R.v3168, N.v3168.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3169 (s : N.State) (i : N.Inputs) :
  R.v3169 (state s) (inputs i) = Zmod.unsigned (N.v3169 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3169 s i)) at 1.
  unfold R.v3169, N.v3169.
  rewrite ?node_3168.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1326_nr_5F1327.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1326_nr_5F1327 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3170 (s : N.State) (i : N.Inputs) :
  R.v3170 (state s) (inputs i) = Zmod.unsigned (N.v3170 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3170 s i)) at 1.
  unfold R.v3170, N.v3170.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3171 (s : N.State) (i : N.Inputs) :
  R.v3171 (state s) (inputs i) = Zmod.unsigned (N.v3171 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3171 s i)) at 1.
  unfold R.v3171, N.v3171.
  rewrite ?node_3170.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1327_nr_5F1328.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1327_nr_5F1328 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3172 (s : N.State) (i : N.Inputs) :
  R.v3172 (state s) (inputs i) = Zmod.unsigned (N.v3172 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3172 s i)) at 1.
  unfold R.v3172, N.v3172.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3173 (s : N.State) (i : N.Inputs) :
  R.v3173 (state s) (inputs i) = Zmod.unsigned (N.v3173 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3173 s i)) at 1.
  unfold R.v3173, N.v3173.
  rewrite ?node_3172.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1328_nr_5F1329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1328_nr_5F1329 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3174 (s : N.State) (i : N.Inputs) :
  R.v3174 (state s) (inputs i) = Zmod.unsigned (N.v3174 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3174 s i)) at 1.
  unfold R.v3174, N.v3174.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3175 (s : N.State) (i : N.Inputs) :
  R.v3175 (state s) (inputs i) = Zmod.unsigned (N.v3175 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3175 s i)) at 1.
  unfold R.v3175, N.v3175.
  rewrite ?node_3174.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1329_nr_5F1330.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1329_nr_5F1330 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3176 (s : N.State) (i : N.Inputs) :
  R.v3176 (state s) (inputs i) = Zmod.unsigned (N.v3176 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3176 s i)) at 1.
  unfold R.v3176, N.v3176.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3177 (s : N.State) (i : N.Inputs) :
  R.v3177 (state s) (inputs i) = Zmod.unsigned (N.v3177 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3177 s i)) at 1.
  unfold R.v3177, N.v3177.
  rewrite ?node_3176.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1330_nr_5F1331.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1330_nr_5F1331 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3178 (s : N.State) (i : N.Inputs) :
  R.v3178 (state s) (inputs i) = Zmod.unsigned (N.v3178 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3178 s i)) at 1.
  unfold R.v3178, N.v3178.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3179 (s : N.State) (i : N.Inputs) :
  R.v3179 (state s) (inputs i) = Zmod.unsigned (N.v3179 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3179 s i)) at 1.
  unfold R.v3179, N.v3179.
  rewrite ?node_3178.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1331_nr_5F1332.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1331_nr_5F1332 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3180 (s : N.State) (i : N.Inputs) :
  R.v3180 (state s) (inputs i) = Zmod.unsigned (N.v3180 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3180 s i)) at 1.
  unfold R.v3180, N.v3180.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3181 (s : N.State) (i : N.Inputs) :
  R.v3181 (state s) (inputs i) = Zmod.unsigned (N.v3181 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3181 s i)) at 1.
  unfold R.v3181, N.v3181.
  rewrite ?node_3180.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1332_nr_5F1333.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1332_nr_5F1333 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3182 (s : N.State) (i : N.Inputs) :
  R.v3182 (state s) (inputs i) = Zmod.unsigned (N.v3182 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3182 s i)) at 1.
  unfold R.v3182, N.v3182.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3183 (s : N.State) (i : N.Inputs) :
  R.v3183 (state s) (inputs i) = Zmod.unsigned (N.v3183 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3183 s i)) at 1.
  unfold R.v3183, N.v3183.
  rewrite ?node_3182.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1333_nr_5F1334.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1333_nr_5F1334 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3184 (s : N.State) (i : N.Inputs) :
  R.v3184 (state s) (inputs i) = Zmod.unsigned (N.v3184 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3184 s i)) at 1.
  unfold R.v3184, N.v3184.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3185 (s : N.State) (i : N.Inputs) :
  R.v3185 (state s) (inputs i) = Zmod.unsigned (N.v3185 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3185 s i)) at 1.
  unfold R.v3185, N.v3185.
  rewrite ?node_3184.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1334_nr_5F1335.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1334_nr_5F1335 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3186 (s : N.State) (i : N.Inputs) :
  R.v3186 (state s) (inputs i) = Zmod.unsigned (N.v3186 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3186 s i)) at 1.
  unfold R.v3186, N.v3186.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3187 (s : N.State) (i : N.Inputs) :
  R.v3187 (state s) (inputs i) = Zmod.unsigned (N.v3187 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3187 s i)) at 1.
  unfold R.v3187, N.v3187.
  rewrite ?node_3186.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1335_nr_5F1336.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1335_nr_5F1336 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3188 (s : N.State) (i : N.Inputs) :
  R.v3188 (state s) (inputs i) = Zmod.unsigned (N.v3188 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3188 s i)) at 1.
  unfold R.v3188, N.v3188.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3189 (s : N.State) (i : N.Inputs) :
  R.v3189 (state s) (inputs i) = Zmod.unsigned (N.v3189 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3189 s i)) at 1.
  unfold R.v3189, N.v3189.
  rewrite ?node_3188.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1336_nr_5F1337.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1336_nr_5F1337 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3190 (s : N.State) (i : N.Inputs) :
  R.v3190 (state s) (inputs i) = Zmod.unsigned (N.v3190 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3190 s i)) at 1.
  unfold R.v3190, N.v3190.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3191 (s : N.State) (i : N.Inputs) :
  R.v3191 (state s) (inputs i) = Zmod.unsigned (N.v3191 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3191 s i)) at 1.
  unfold R.v3191, N.v3191.
  rewrite ?node_3190.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1337_nr_5F1338.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1337_nr_5F1338 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3192 (s : N.State) (i : N.Inputs) :
  R.v3192 (state s) (inputs i) = Zmod.unsigned (N.v3192 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3192 s i)) at 1.
  unfold R.v3192, N.v3192.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3193 (s : N.State) (i : N.Inputs) :
  R.v3193 (state s) (inputs i) = Zmod.unsigned (N.v3193 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3193 s i)) at 1.
  unfold R.v3193, N.v3193.
  rewrite ?node_3192.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1338_nr_5F1339.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1338_nr_5F1339 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3194 (s : N.State) (i : N.Inputs) :
  R.v3194 (state s) (inputs i) = Zmod.unsigned (N.v3194 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3194 s i)) at 1.
  unfold R.v3194, N.v3194.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3195 (s : N.State) (i : N.Inputs) :
  R.v3195 (state s) (inputs i) = Zmod.unsigned (N.v3195 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3195 s i)) at 1.
  unfold R.v3195, N.v3195.
  rewrite ?node_3194.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1339_nr_5F1340.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1339_nr_5F1340 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3196 (s : N.State) (i : N.Inputs) :
  R.v3196 (state s) (inputs i) = Zmod.unsigned (N.v3196 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3196 s i)) at 1.
  unfold R.v3196, N.v3196.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3197 (s : N.State) (i : N.Inputs) :
  R.v3197 (state s) (inputs i) = Zmod.unsigned (N.v3197 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3197 s i)) at 1.
  unfold R.v3197, N.v3197.
  rewrite ?node_3196.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1340_nr_5F1341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1340_nr_5F1341 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3198 (s : N.State) (i : N.Inputs) :
  R.v3198 (state s) (inputs i) = Zmod.unsigned (N.v3198 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3198 s i)) at 1.
  unfold R.v3198, N.v3198.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3199 (s : N.State) (i : N.Inputs) :
  R.v3199 (state s) (inputs i) = Zmod.unsigned (N.v3199 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3199 s i)) at 1.
  unfold R.v3199, N.v3199.
  rewrite ?node_3198.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1341_nr_5F1342.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1341_nr_5F1342 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3200 (s : N.State) (i : N.Inputs) :
  R.v3200 (state s) (inputs i) = Zmod.unsigned (N.v3200 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3200 s i)) at 1.
  unfold R.v3200, N.v3200.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3201 (s : N.State) (i : N.Inputs) :
  R.v3201 (state s) (inputs i) = Zmod.unsigned (N.v3201 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3201 s i)) at 1.
  unfold R.v3201, N.v3201.
  rewrite ?node_3200.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1342_nr_5F1343.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1342_nr_5F1343 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3202 (s : N.State) (i : N.Inputs) :
  R.v3202 (state s) (inputs i) = Zmod.unsigned (N.v3202 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3202 s i)) at 1.
  unfold R.v3202, N.v3202.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3203 (s : N.State) (i : N.Inputs) :
  R.v3203 (state s) (inputs i) = Zmod.unsigned (N.v3203 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3203 s i)) at 1.
  unfold R.v3203, N.v3203.
  rewrite ?node_3202.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1343_nr_5F1344.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1343_nr_5F1344 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3204 (s : N.State) (i : N.Inputs) :
  R.v3204 (state s) (inputs i) = Zmod.unsigned (N.v3204 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3204 s i)) at 1.
  unfold R.v3204, N.v3204.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3205 (s : N.State) (i : N.Inputs) :
  R.v3205 (state s) (inputs i) = Zmod.unsigned (N.v3205 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3205 s i)) at 1.
  unfold R.v3205, N.v3205.
  rewrite ?node_3204.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1344_nr_5F1345.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1344_nr_5F1345 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3206 (s : N.State) (i : N.Inputs) :
  R.v3206 (state s) (inputs i) = Zmod.unsigned (N.v3206 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3206 s i)) at 1.
  unfold R.v3206, N.v3206.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3207 (s : N.State) (i : N.Inputs) :
  R.v3207 (state s) (inputs i) = Zmod.unsigned (N.v3207 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3207 s i)) at 1.
  unfold R.v3207, N.v3207.
  rewrite ?node_3206.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1345_nr_5F1346.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1345_nr_5F1346 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3208 (s : N.State) (i : N.Inputs) :
  R.v3208 (state s) (inputs i) = Zmod.unsigned (N.v3208 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3208 s i)) at 1.
  unfold R.v3208, N.v3208.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3209 (s : N.State) (i : N.Inputs) :
  R.v3209 (state s) (inputs i) = Zmod.unsigned (N.v3209 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3209 s i)) at 1.
  unfold R.v3209, N.v3209.
  rewrite ?node_3208.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1346_nr_5F1347.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1346_nr_5F1347 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3210 (s : N.State) (i : N.Inputs) :
  R.v3210 (state s) (inputs i) = Zmod.unsigned (N.v3210 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3210 s i)) at 1.
  unfold R.v3210, N.v3210.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3211 (s : N.State) (i : N.Inputs) :
  R.v3211 (state s) (inputs i) = Zmod.unsigned (N.v3211 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3211 s i)) at 1.
  unfold R.v3211, N.v3211.
  rewrite ?node_3210.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1347_nr_5F1348.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1347_nr_5F1348 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3212 (s : N.State) (i : N.Inputs) :
  R.v3212 (state s) (inputs i) = Zmod.unsigned (N.v3212 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3212 s i)) at 1.
  unfold R.v3212, N.v3212.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3213 (s : N.State) (i : N.Inputs) :
  R.v3213 (state s) (inputs i) = Zmod.unsigned (N.v3213 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3213 s i)) at 1.
  unfold R.v3213, N.v3213.
  rewrite ?node_3212.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1348_nr_5F1349.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1348_nr_5F1349 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3214 (s : N.State) (i : N.Inputs) :
  R.v3214 (state s) (inputs i) = Zmod.unsigned (N.v3214 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3214 s i)) at 1.
  unfold R.v3214, N.v3214.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3215 (s : N.State) (i : N.Inputs) :
  R.v3215 (state s) (inputs i) = Zmod.unsigned (N.v3215 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3215 s i)) at 1.
  unfold R.v3215, N.v3215.
  rewrite ?node_3214.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1349_nr_5F1351.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1349_nr_5F1351 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3216 (s : N.State) (i : N.Inputs) :
  R.v3216 (state s) (inputs i) = Zmod.unsigned (N.v3216 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3216 s i)) at 1.
  unfold R.v3216, N.v3216.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3217 (s : N.State) (i : N.Inputs) :
  R.v3217 (state s) (inputs i) = Zmod.unsigned (N.v3217 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3217 s i)) at 1.
  unfold R.v3217, N.v3217.
  rewrite ?node_3216.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1350_nr_5F1352.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1350_nr_5F1352 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3218 (s : N.State) (i : N.Inputs) :
  R.v3218 (state s) (inputs i) = Zmod.unsigned (N.v3218 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3218 s i)) at 1.
  unfold R.v3218, N.v3218.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3219 (s : N.State) (i : N.Inputs) :
  R.v3219 (state s) (inputs i) = Zmod.unsigned (N.v3219 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3219 s i)) at 1.
  unfold R.v3219, N.v3219.
  rewrite ?node_3218.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1351_nr_5F1353.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1351_nr_5F1353 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3220 (s : N.State) (i : N.Inputs) :
  R.v3220 (state s) (inputs i) = Zmod.unsigned (N.v3220 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3220 s i)) at 1.
  unfold R.v3220, N.v3220.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3221 (s : N.State) (i : N.Inputs) :
  R.v3221 (state s) (inputs i) = Zmod.unsigned (N.v3221 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3221 s i)) at 1.
  unfold R.v3221, N.v3221.
  rewrite ?node_3220.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1352_nr_5F1354.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1352_nr_5F1354 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3222 (s : N.State) (i : N.Inputs) :
  R.v3222 (state s) (inputs i) = Zmod.unsigned (N.v3222 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3222 s i)) at 1.
  unfold R.v3222, N.v3222.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3223 (s : N.State) (i : N.Inputs) :
  R.v3223 (state s) (inputs i) = Zmod.unsigned (N.v3223 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3223 s i)) at 1.
  unfold R.v3223, N.v3223.
  rewrite ?node_3222.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1353_nr_5F1355.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1353_nr_5F1355 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3224 (s : N.State) (i : N.Inputs) :
  R.v3224 (state s) (inputs i) = Zmod.unsigned (N.v3224 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3224 s i)) at 1.
  unfold R.v3224, N.v3224.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3225 (s : N.State) (i : N.Inputs) :
  R.v3225 (state s) (inputs i) = Zmod.unsigned (N.v3225 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3225 s i)) at 1.
  unfold R.v3225, N.v3225.
  rewrite ?node_3224.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1354_nr_5F1356.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1354_nr_5F1356 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3226 (s : N.State) (i : N.Inputs) :
  R.v3226 (state s) (inputs i) = Zmod.unsigned (N.v3226 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3226 s i)) at 1.
  unfold R.v3226, N.v3226.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3227 (s : N.State) (i : N.Inputs) :
  R.v3227 (state s) (inputs i) = Zmod.unsigned (N.v3227 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3227 s i)) at 1.
  unfold R.v3227, N.v3227.
  rewrite ?node_3226.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1355_nr_5F1357.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1355_nr_5F1357 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3228 (s : N.State) (i : N.Inputs) :
  R.v3228 (state s) (inputs i) = Zmod.unsigned (N.v3228 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3228 s i)) at 1.
  unfold R.v3228, N.v3228.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3229 (s : N.State) (i : N.Inputs) :
  R.v3229 (state s) (inputs i) = Zmod.unsigned (N.v3229 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3229 s i)) at 1.
  unfold R.v3229, N.v3229.
  rewrite ?node_3228.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1356_nr_5F1358.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1356_nr_5F1358 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3230 (s : N.State) (i : N.Inputs) :
  R.v3230 (state s) (inputs i) = Zmod.unsigned (N.v3230 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3230 s i)) at 1.
  unfold R.v3230, N.v3230.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3231 (s : N.State) (i : N.Inputs) :
  R.v3231 (state s) (inputs i) = Zmod.unsigned (N.v3231 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3231 s i)) at 1.
  unfold R.v3231, N.v3231.
  rewrite ?node_3230.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1357_nr_5F1359.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1357_nr_5F1359 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3232 (s : N.State) (i : N.Inputs) :
  R.v3232 (state s) (inputs i) = Zmod.unsigned (N.v3232 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3232 s i)) at 1.
  unfold R.v3232, N.v3232.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3233 (s : N.State) (i : N.Inputs) :
  R.v3233 (state s) (inputs i) = Zmod.unsigned (N.v3233 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3233 s i)) at 1.
  unfold R.v3233, N.v3233.
  rewrite ?node_3232.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1358_nr_5F1360.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1358_nr_5F1360 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3234 (s : N.State) (i : N.Inputs) :
  R.v3234 (state s) (inputs i) = Zmod.unsigned (N.v3234 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3234 s i)) at 1.
  unfold R.v3234, N.v3234.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3235 (s : N.State) (i : N.Inputs) :
  R.v3235 (state s) (inputs i) = Zmod.unsigned (N.v3235 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3235 s i)) at 1.
  unfold R.v3235, N.v3235.
  rewrite ?node_3234.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1359_nr_5F1361.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1359_nr_5F1361 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3236 (s : N.State) (i : N.Inputs) :
  R.v3236 (state s) (inputs i) = Zmod.unsigned (N.v3236 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3236 s i)) at 1.
  unfold R.v3236, N.v3236.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3237 (s : N.State) (i : N.Inputs) :
  R.v3237 (state s) (inputs i) = Zmod.unsigned (N.v3237 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3237 s i)) at 1.
  unfold R.v3237, N.v3237.
  rewrite ?node_3236.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1360_nr_5F1362.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1360_nr_5F1362 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3238 (s : N.State) (i : N.Inputs) :
  R.v3238 (state s) (inputs i) = Zmod.unsigned (N.v3238 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3238 s i)) at 1.
  unfold R.v3238, N.v3238.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3239 (s : N.State) (i : N.Inputs) :
  R.v3239 (state s) (inputs i) = Zmod.unsigned (N.v3239 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3239 s i)) at 1.
  unfold R.v3239, N.v3239.
  rewrite ?node_3238.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1361_nr_5F1363.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1361_nr_5F1363 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3240 (s : N.State) (i : N.Inputs) :
  R.v3240 (state s) (inputs i) = Zmod.unsigned (N.v3240 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3240 s i)) at 1.
  unfold R.v3240, N.v3240.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3241 (s : N.State) (i : N.Inputs) :
  R.v3241 (state s) (inputs i) = Zmod.unsigned (N.v3241 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3241 s i)) at 1.
  unfold R.v3241, N.v3241.
  rewrite ?node_3240.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1362_nr_5F1364.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1362_nr_5F1364 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3242 (s : N.State) (i : N.Inputs) :
  R.v3242 (state s) (inputs i) = Zmod.unsigned (N.v3242 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3242 s i)) at 1.
  unfold R.v3242, N.v3242.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3243 (s : N.State) (i : N.Inputs) :
  R.v3243 (state s) (inputs i) = Zmod.unsigned (N.v3243 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3243 s i)) at 1.
  unfold R.v3243, N.v3243.
  rewrite ?node_3242.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1363_nr_5F1365.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1363_nr_5F1365 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3244 (s : N.State) (i : N.Inputs) :
  R.v3244 (state s) (inputs i) = Zmod.unsigned (N.v3244 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3244 s i)) at 1.
  unfold R.v3244, N.v3244.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3245 (s : N.State) (i : N.Inputs) :
  R.v3245 (state s) (inputs i) = Zmod.unsigned (N.v3245 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3245 s i)) at 1.
  unfold R.v3245, N.v3245.
  rewrite ?node_3244.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1364_nr_5F1366.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1364_nr_5F1366 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3246 (s : N.State) (i : N.Inputs) :
  R.v3246 (state s) (inputs i) = Zmod.unsigned (N.v3246 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3246 s i)) at 1.
  unfold R.v3246, N.v3246.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3247 (s : N.State) (i : N.Inputs) :
  R.v3247 (state s) (inputs i) = Zmod.unsigned (N.v3247 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3247 s i)) at 1.
  unfold R.v3247, N.v3247.
  rewrite ?node_3246.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1365_nr_5F1367.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1365_nr_5F1367 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3248 (s : N.State) (i : N.Inputs) :
  R.v3248 (state s) (inputs i) = Zmod.unsigned (N.v3248 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3248 s i)) at 1.
  unfold R.v3248, N.v3248.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3249 (s : N.State) (i : N.Inputs) :
  R.v3249 (state s) (inputs i) = Zmod.unsigned (N.v3249 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3249 s i)) at 1.
  unfold R.v3249, N.v3249.
  rewrite ?node_3248.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1366_nr_5F1368.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1366_nr_5F1368 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3250 (s : N.State) (i : N.Inputs) :
  R.v3250 (state s) (inputs i) = Zmod.unsigned (N.v3250 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3250 s i)) at 1.
  unfold R.v3250, N.v3250.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3251 (s : N.State) (i : N.Inputs) :
  R.v3251 (state s) (inputs i) = Zmod.unsigned (N.v3251 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3251 s i)) at 1.
  unfold R.v3251, N.v3251.
  rewrite ?node_3250.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1367_nr_5F1369.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1367_nr_5F1369 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3252 (s : N.State) (i : N.Inputs) :
  R.v3252 (state s) (inputs i) = Zmod.unsigned (N.v3252 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3252 s i)) at 1.
  unfold R.v3252, N.v3252.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3253 (s : N.State) (i : N.Inputs) :
  R.v3253 (state s) (inputs i) = Zmod.unsigned (N.v3253 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3253 s i)) at 1.
  unfold R.v3253, N.v3253.
  rewrite ?node_3252.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1368_nr_5F1370.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1368_nr_5F1370 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3254 (s : N.State) (i : N.Inputs) :
  R.v3254 (state s) (inputs i) = Zmod.unsigned (N.v3254 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3254 s i)) at 1.
  unfold R.v3254, N.v3254.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3255 (s : N.State) (i : N.Inputs) :
  R.v3255 (state s) (inputs i) = Zmod.unsigned (N.v3255 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3255 s i)) at 1.
  unfold R.v3255, N.v3255.
  rewrite ?node_3254.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1369_nr_5F1371.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1369_nr_5F1371 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3256 (s : N.State) (i : N.Inputs) :
  R.v3256 (state s) (inputs i) = Zmod.unsigned (N.v3256 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3256 s i)) at 1.
  unfold R.v3256, N.v3256.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3257 (s : N.State) (i : N.Inputs) :
  R.v3257 (state s) (inputs i) = Zmod.unsigned (N.v3257 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3257 s i)) at 1.
  unfold R.v3257, N.v3257.
  rewrite ?node_3256.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1370_nr_5F1372.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1370_nr_5F1372 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3258 (s : N.State) (i : N.Inputs) :
  R.v3258 (state s) (inputs i) = Zmod.unsigned (N.v3258 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3258 s i)) at 1.
  unfold R.v3258, N.v3258.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3259 (s : N.State) (i : N.Inputs) :
  R.v3259 (state s) (inputs i) = Zmod.unsigned (N.v3259 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3259 s i)) at 1.
  unfold R.v3259, N.v3259.
  rewrite ?node_3258.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1371_nr_5F1373.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1371_nr_5F1373 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3260 (s : N.State) (i : N.Inputs) :
  R.v3260 (state s) (inputs i) = Zmod.unsigned (N.v3260 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3260 s i)) at 1.
  unfold R.v3260, N.v3260.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3261 (s : N.State) (i : N.Inputs) :
  R.v3261 (state s) (inputs i) = Zmod.unsigned (N.v3261 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3261 s i)) at 1.
  unfold R.v3261, N.v3261.
  rewrite ?node_3260.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1372_nr_5F1374.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1372_nr_5F1374 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3262 (s : N.State) (i : N.Inputs) :
  R.v3262 (state s) (inputs i) = Zmod.unsigned (N.v3262 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3262 s i)) at 1.
  unfold R.v3262, N.v3262.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3263 (s : N.State) (i : N.Inputs) :
  R.v3263 (state s) (inputs i) = Zmod.unsigned (N.v3263 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3263 s i)) at 1.
  unfold R.v3263, N.v3263.
  rewrite ?node_3262.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1373_nr_5F1375.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1373_nr_5F1375 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3264 (s : N.State) (i : N.Inputs) :
  R.v3264 (state s) (inputs i) = Zmod.unsigned (N.v3264 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3264 s i)) at 1.
  unfold R.v3264, N.v3264.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3265 (s : N.State) (i : N.Inputs) :
  R.v3265 (state s) (inputs i) = Zmod.unsigned (N.v3265 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3265 s i)) at 1.
  unfold R.v3265, N.v3265.
  rewrite ?node_3264.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1374_nr_5F1376.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1374_nr_5F1376 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3266 (s : N.State) (i : N.Inputs) :
  R.v3266 (state s) (inputs i) = Zmod.unsigned (N.v3266 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3266 s i)) at 1.
  unfold R.v3266, N.v3266.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3267 (s : N.State) (i : N.Inputs) :
  R.v3267 (state s) (inputs i) = Zmod.unsigned (N.v3267 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3267 s i)) at 1.
  unfold R.v3267, N.v3267.
  rewrite ?node_3266.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1375_nr_5F1377.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1375_nr_5F1377 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3268 (s : N.State) (i : N.Inputs) :
  R.v3268 (state s) (inputs i) = Zmod.unsigned (N.v3268 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3268 s i)) at 1.
  unfold R.v3268, N.v3268.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3269 (s : N.State) (i : N.Inputs) :
  R.v3269 (state s) (inputs i) = Zmod.unsigned (N.v3269 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3269 s i)) at 1.
  unfold R.v3269, N.v3269.
  rewrite ?node_3268.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1376_nr_5F1378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1376_nr_5F1378 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3270 (s : N.State) (i : N.Inputs) :
  R.v3270 (state s) (inputs i) = Zmod.unsigned (N.v3270 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3270 s i)) at 1.
  unfold R.v3270, N.v3270.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3271 (s : N.State) (i : N.Inputs) :
  R.v3271 (state s) (inputs i) = Zmod.unsigned (N.v3271 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3271 s i)) at 1.
  unfold R.v3271, N.v3271.
  rewrite ?node_3270.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1377_nr_5F1379.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1377_nr_5F1379 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3272 (s : N.State) (i : N.Inputs) :
  R.v3272 (state s) (inputs i) = Zmod.unsigned (N.v3272 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3272 s i)) at 1.
  unfold R.v3272, N.v3272.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3273 (s : N.State) (i : N.Inputs) :
  R.v3273 (state s) (inputs i) = Zmod.unsigned (N.v3273 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3273 s i)) at 1.
  unfold R.v3273, N.v3273.
  rewrite ?node_3272.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1378_nr_5F1380.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1378_nr_5F1380 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3274 (s : N.State) (i : N.Inputs) :
  R.v3274 (state s) (inputs i) = Zmod.unsigned (N.v3274 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3274 s i)) at 1.
  unfold R.v3274, N.v3274.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3275 (s : N.State) (i : N.Inputs) :
  R.v3275 (state s) (inputs i) = Zmod.unsigned (N.v3275 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3275 s i)) at 1.
  unfold R.v3275, N.v3275.
  unfold R.v3021, N.v3021.
  rewrite ?node_3274.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3276 (s : N.State) (i : N.Inputs) :
  R.v3276 (state s) (inputs i) = Zmod.unsigned (N.v3276 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3276 s i)) at 1.
  unfold R.v3276, N.v3276.
  rewrite ?node_3275.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1379_nr_5F1381.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1379_nr_5F1381 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3277 (s : N.State) (i : N.Inputs) :
  R.v3277 (state s) (inputs i) = Zmod.unsigned (N.v3277 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3277 s i)) at 1.
  unfold R.v3277, N.v3277.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3278 (s : N.State) (i : N.Inputs) :
  R.v3278 (state s) (inputs i) = Zmod.unsigned (N.v3278 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3278 s i)) at 1.
  unfold R.v3278, N.v3278.
  rewrite ?node_3277.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1380_nr_5F1382.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1380_nr_5F1382 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3279 (s : N.State) (i : N.Inputs) :
  R.v3279 (state s) (inputs i) = Zmod.unsigned (N.v3279 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3279 s i)) at 1.
  unfold R.v3279, N.v3279.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3280 (s : N.State) (i : N.Inputs) :
  R.v3280 (state s) (inputs i) = Zmod.unsigned (N.v3280 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3280 s i)) at 1.
  unfold R.v3280, N.v3280.
  rewrite ?node_3279.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1381_nr_5F1383.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1381_nr_5F1383 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3281 (s : N.State) (i : N.Inputs) :
  R.v3281 (state s) (inputs i) = Zmod.unsigned (N.v3281 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3281 s i)) at 1.
  unfold R.v3281, N.v3281.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3282 (s : N.State) (i : N.Inputs) :
  R.v3282 (state s) (inputs i) = Zmod.unsigned (N.v3282 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3282 s i)) at 1.
  unfold R.v3282, N.v3282.
  rewrite ?node_3281.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1382_nr_5F1384.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1382_nr_5F1384 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3283 (s : N.State) (i : N.Inputs) :
  R.v3283 (state s) (inputs i) = Zmod.unsigned (N.v3283 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3283 s i)) at 1.
  unfold R.v3283, N.v3283.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3284 (s : N.State) (i : N.Inputs) :
  R.v3284 (state s) (inputs i) = Zmod.unsigned (N.v3284 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3284 s i)) at 1.
  unfold R.v3284, N.v3284.
  rewrite ?node_3283.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1383_nr_5F1385.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1383_nr_5F1385 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3285 (s : N.State) (i : N.Inputs) :
  R.v3285 (state s) (inputs i) = Zmod.unsigned (N.v3285 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3285 s i)) at 1.
  unfold R.v3285, N.v3285.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3286 (s : N.State) (i : N.Inputs) :
  R.v3286 (state s) (inputs i) = Zmod.unsigned (N.v3286 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3286 s i)) at 1.
  unfold R.v3286, N.v3286.
  rewrite ?node_3285.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1384_nr_5F1386.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1384_nr_5F1386 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3287 (s : N.State) (i : N.Inputs) :
  R.v3287 (state s) (inputs i) = Zmod.unsigned (N.v3287 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3287 s i)) at 1.
  unfold R.v3287, N.v3287.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3288 (s : N.State) (i : N.Inputs) :
  R.v3288 (state s) (inputs i) = Zmod.unsigned (N.v3288 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3288 s i)) at 1.
  unfold R.v3288, N.v3288.
  rewrite ?node_3287.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1385_nr_5F1387.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1385_nr_5F1387 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3289 (s : N.State) (i : N.Inputs) :
  R.v3289 (state s) (inputs i) = Zmod.unsigned (N.v3289 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3289 s i)) at 1.
  unfold R.v3289, N.v3289.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3290 (s : N.State) (i : N.Inputs) :
  R.v3290 (state s) (inputs i) = Zmod.unsigned (N.v3290 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3290 s i)) at 1.
  unfold R.v3290, N.v3290.
  rewrite ?node_3289.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1386_nr_5F1388.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1386_nr_5F1388 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3291 (s : N.State) (i : N.Inputs) :
  R.v3291 (state s) (inputs i) = Zmod.unsigned (N.v3291 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3291 s i)) at 1.
  unfold R.v3291, N.v3291.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3292 (s : N.State) (i : N.Inputs) :
  R.v3292 (state s) (inputs i) = Zmod.unsigned (N.v3292 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3292 s i)) at 1.
  unfold R.v3292, N.v3292.
  rewrite ?node_3291.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1387_nr_5F1389.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1387_nr_5F1389 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3293 (s : N.State) (i : N.Inputs) :
  R.v3293 (state s) (inputs i) = Zmod.unsigned (N.v3293 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3293 s i)) at 1.
  unfold R.v3293, N.v3293.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3294 (s : N.State) (i : N.Inputs) :
  R.v3294 (state s) (inputs i) = Zmod.unsigned (N.v3294 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3294 s i)) at 1.
  unfold R.v3294, N.v3294.
  rewrite ?node_3293.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1388_nr_5F1390.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1388_nr_5F1390 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3295 (s : N.State) (i : N.Inputs) :
  R.v3295 (state s) (inputs i) = Zmod.unsigned (N.v3295 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3295 s i)) at 1.
  unfold R.v3295, N.v3295.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3296 (s : N.State) (i : N.Inputs) :
  R.v3296 (state s) (inputs i) = Zmod.unsigned (N.v3296 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3296 s i)) at 1.
  unfold R.v3296, N.v3296.
  rewrite ?node_3295.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1389_nr_5F1391.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1389_nr_5F1391 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3297 (s : N.State) (i : N.Inputs) :
  R.v3297 (state s) (inputs i) = Zmod.unsigned (N.v3297 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3297 s i)) at 1.
  unfold R.v3297, N.v3297.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3298 (s : N.State) (i : N.Inputs) :
  R.v3298 (state s) (inputs i) = Zmod.unsigned (N.v3298 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3298 s i)) at 1.
  unfold R.v3298, N.v3298.
  rewrite ?node_3297.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1390_nr_5F1392.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1390_nr_5F1392 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3299 (s : N.State) (i : N.Inputs) :
  R.v3299 (state s) (inputs i) = Zmod.unsigned (N.v3299 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3299 s i)) at 1.
  unfold R.v3299, N.v3299.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3300 (s : N.State) (i : N.Inputs) :
  R.v3300 (state s) (inputs i) = Zmod.unsigned (N.v3300 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3300 s i)) at 1.
  unfold R.v3300, N.v3300.
  rewrite ?node_3299.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1391_nr_5F1393.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1391_nr_5F1393 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3301 (s : N.State) (i : N.Inputs) :
  R.v3301 (state s) (inputs i) = Zmod.unsigned (N.v3301 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3301 s i)) at 1.
  unfold R.v3301, N.v3301.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3302 (s : N.State) (i : N.Inputs) :
  R.v3302 (state s) (inputs i) = Zmod.unsigned (N.v3302 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3302 s i)) at 1.
  unfold R.v3302, N.v3302.
  rewrite ?node_3301.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1392_nr_5F1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1392_nr_5F1394 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3303 (s : N.State) (i : N.Inputs) :
  R.v3303 (state s) (inputs i) = Zmod.unsigned (N.v3303 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3303 s i)) at 1.
  unfold R.v3303, N.v3303.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3304 (s : N.State) (i : N.Inputs) :
  R.v3304 (state s) (inputs i) = Zmod.unsigned (N.v3304 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3304 s i)) at 1.
  unfold R.v3304, N.v3304.
  rewrite ?node_3303.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1393_nr_5F1395.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1393_nr_5F1395 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3305 (s : N.State) (i : N.Inputs) :
  R.v3305 (state s) (inputs i) = Zmod.unsigned (N.v3305 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3305 s i)) at 1.
  unfold R.v3305, N.v3305.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3306 (s : N.State) (i : N.Inputs) :
  R.v3306 (state s) (inputs i) = Zmod.unsigned (N.v3306 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3306 s i)) at 1.
  unfold R.v3306, N.v3306.
  rewrite ?node_3305.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1394_nr_5F1396.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1394_nr_5F1396 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3307 (s : N.State) (i : N.Inputs) :
  R.v3307 (state s) (inputs i) = Zmod.unsigned (N.v3307 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3307 s i)) at 1.
  unfold R.v3307, N.v3307.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3308 (s : N.State) (i : N.Inputs) :
  R.v3308 (state s) (inputs i) = Zmod.unsigned (N.v3308 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3308 s i)) at 1.
  unfold R.v3308, N.v3308.
  rewrite ?node_3307.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1395_nr_5F1397.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1395_nr_5F1397 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3309 (s : N.State) (i : N.Inputs) :
  R.v3309 (state s) (inputs i) = Zmod.unsigned (N.v3309 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3309 s i)) at 1.
  unfold R.v3309, N.v3309.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3310 (s : N.State) (i : N.Inputs) :
  R.v3310 (state s) (inputs i) = Zmod.unsigned (N.v3310 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3310 s i)) at 1.
  unfold R.v3310, N.v3310.
  rewrite ?node_3309.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1396_nr_5F1398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1396_nr_5F1398 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3311 (s : N.State) (i : N.Inputs) :
  R.v3311 (state s) (inputs i) = Zmod.unsigned (N.v3311 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3311 s i)) at 1.
  unfold R.v3311, N.v3311.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3312 (s : N.State) (i : N.Inputs) :
  R.v3312 (state s) (inputs i) = Zmod.unsigned (N.v3312 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3312 s i)) at 1.
  unfold R.v3312, N.v3312.
  rewrite ?node_3311.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1397_nr_5F1399.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1397_nr_5F1399 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3313 (s : N.State) (i : N.Inputs) :
  R.v3313 (state s) (inputs i) = Zmod.unsigned (N.v3313 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3313 s i)) at 1.
  unfold R.v3313, N.v3313.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3314 (s : N.State) (i : N.Inputs) :
  R.v3314 (state s) (inputs i) = Zmod.unsigned (N.v3314 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3314 s i)) at 1.
  unfold R.v3314, N.v3314.
  rewrite ?node_3313.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1398_nr_5F1400.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1398_nr_5F1400 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3315 (s : N.State) (i : N.Inputs) :
  R.v3315 (state s) (inputs i) = Zmod.unsigned (N.v3315 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3315 s i)) at 1.
  unfold R.v3315, N.v3315.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3316 (s : N.State) (i : N.Inputs) :
  R.v3316 (state s) (inputs i) = Zmod.unsigned (N.v3316 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3316 s i)) at 1.
  unfold R.v3316, N.v3316.
  rewrite ?node_3315.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1399_nr_5F1401.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1399_nr_5F1401 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3317 (s : N.State) (i : N.Inputs) :
  R.v3317 (state s) (inputs i) = Zmod.unsigned (N.v3317 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3317 s i)) at 1.
  unfold R.v3317, N.v3317.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3318 (s : N.State) (i : N.Inputs) :
  R.v3318 (state s) (inputs i) = Zmod.unsigned (N.v3318 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3318 s i)) at 1.
  unfold R.v3318, N.v3318.
  rewrite ?node_3317.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1400_nr_5F1402.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1400_nr_5F1402 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3319 (s : N.State) (i : N.Inputs) :
  R.v3319 (state s) (inputs i) = Zmod.unsigned (N.v3319 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3319 s i)) at 1.
  unfold R.v3319, N.v3319.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3320 (s : N.State) (i : N.Inputs) :
  R.v3320 (state s) (inputs i) = Zmod.unsigned (N.v3320 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3320 s i)) at 1.
  unfold R.v3320, N.v3320.
  rewrite ?node_3319.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1401_nr_5F1403.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1401_nr_5F1403 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3321 (s : N.State) (i : N.Inputs) :
  R.v3321 (state s) (inputs i) = Zmod.unsigned (N.v3321 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3321 s i)) at 1.
  unfold R.v3321, N.v3321.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3322 (s : N.State) (i : N.Inputs) :
  R.v3322 (state s) (inputs i) = Zmod.unsigned (N.v3322 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3322 s i)) at 1.
  unfold R.v3322, N.v3322.
  rewrite ?node_3321.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1402_nr_5F1404.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1402_nr_5F1404 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3323 (s : N.State) (i : N.Inputs) :
  R.v3323 (state s) (inputs i) = Zmod.unsigned (N.v3323 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3323 s i)) at 1.
  unfold R.v3323, N.v3323.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3324 (s : N.State) (i : N.Inputs) :
  R.v3324 (state s) (inputs i) = Zmod.unsigned (N.v3324 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3324 s i)) at 1.
  unfold R.v3324, N.v3324.
  rewrite ?node_3323.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1403_nr_5F1405.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1403_nr_5F1405 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3325 (s : N.State) (i : N.Inputs) :
  R.v3325 (state s) (inputs i) = Zmod.unsigned (N.v3325 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3325 s i)) at 1.
  unfold R.v3325, N.v3325.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3326 (s : N.State) (i : N.Inputs) :
  R.v3326 (state s) (inputs i) = Zmod.unsigned (N.v3326 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3326 s i)) at 1.
  unfold R.v3326, N.v3326.
  rewrite ?node_3325.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1404_nr_5F1406.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1404_nr_5F1406 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3327 (s : N.State) (i : N.Inputs) :
  R.v3327 (state s) (inputs i) = Zmod.unsigned (N.v3327 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3327 s i)) at 1.
  unfold R.v3327, N.v3327.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3328 (s : N.State) (i : N.Inputs) :
  R.v3328 (state s) (inputs i) = Zmod.unsigned (N.v3328 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3328 s i)) at 1.
  unfold R.v3328, N.v3328.
  rewrite ?node_3327.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1405_nr_5F1407.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1405_nr_5F1407 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3329 (s : N.State) (i : N.Inputs) :
  R.v3329 (state s) (inputs i) = Zmod.unsigned (N.v3329 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3329 s i)) at 1.
  unfold R.v3329, N.v3329.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3330 (s : N.State) (i : N.Inputs) :
  R.v3330 (state s) (inputs i) = Zmod.unsigned (N.v3330 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3330 s i)) at 1.
  unfold R.v3330, N.v3330.
  rewrite ?node_3329.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1406_nr_5F1408.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1406_nr_5F1408 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3331 (s : N.State) (i : N.Inputs) :
  R.v3331 (state s) (inputs i) = Zmod.unsigned (N.v3331 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3331 s i)) at 1.
  unfold R.v3331, N.v3331.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3332 (s : N.State) (i : N.Inputs) :
  R.v3332 (state s) (inputs i) = Zmod.unsigned (N.v3332 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3332 s i)) at 1.
  unfold R.v3332, N.v3332.
  rewrite ?node_3331.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1407_nr_5F1409.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1407_nr_5F1409 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3333 (s : N.State) (i : N.Inputs) :
  R.v3333 (state s) (inputs i) = Zmod.unsigned (N.v3333 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3333 s i)) at 1.
  unfold R.v3333, N.v3333.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3334 (s : N.State) (i : N.Inputs) :
  R.v3334 (state s) (inputs i) = Zmod.unsigned (N.v3334 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3334 s i)) at 1.
  unfold R.v3334, N.v3334.
  rewrite ?node_3333.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1408_nr_5F1410.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1408_nr_5F1410 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3335 (s : N.State) (i : N.Inputs) :
  R.v3335 (state s) (inputs i) = Zmod.unsigned (N.v3335 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3335 s i)) at 1.
  unfold R.v3335, N.v3335.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3336 (s : N.State) (i : N.Inputs) :
  R.v3336 (state s) (inputs i) = Zmod.unsigned (N.v3336 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3336 s i)) at 1.
  unfold R.v3336, N.v3336.
  rewrite ?node_3335.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1409_nr_5F1412.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1409_nr_5F1412 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3337 (s : N.State) (i : N.Inputs) :
  R.v3337 (state s) (inputs i) = Zmod.unsigned (N.v3337 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3337 s i)) at 1.
  unfold R.v3337, N.v3337.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3338 (s : N.State) (i : N.Inputs) :
  R.v3338 (state s) (inputs i) = Zmod.unsigned (N.v3338 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3338 s i)) at 1.
  unfold R.v3338, N.v3338.
  rewrite ?node_3337.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1410_nr_5F1413.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1410_nr_5F1413 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3339 (s : N.State) (i : N.Inputs) :
  R.v3339 (state s) (inputs i) = Zmod.unsigned (N.v3339 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3339 s i)) at 1.
  unfold R.v3339, N.v3339.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3340 (s : N.State) (i : N.Inputs) :
  R.v3340 (state s) (inputs i) = Zmod.unsigned (N.v3340 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3340 s i)) at 1.
  unfold R.v3340, N.v3340.
  rewrite ?node_3339.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1411_nr_5F1414.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1411_nr_5F1414 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3341 (s : N.State) (i : N.Inputs) :
  R.v3341 (state s) (inputs i) = Zmod.unsigned (N.v3341 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3341 s i)) at 1.
  unfold R.v3341, N.v3341.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3342 (s : N.State) (i : N.Inputs) :
  R.v3342 (state s) (inputs i) = Zmod.unsigned (N.v3342 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3342 s i)) at 1.
  unfold R.v3342, N.v3342.
  rewrite ?node_3341.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1412_nr_5F1415.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1412_nr_5F1415 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3343 (s : N.State) (i : N.Inputs) :
  R.v3343 (state s) (inputs i) = Zmod.unsigned (N.v3343 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3343 s i)) at 1.
  unfold R.v3343, N.v3343.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3344 (s : N.State) (i : N.Inputs) :
  R.v3344 (state s) (inputs i) = Zmod.unsigned (N.v3344 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3344 s i)) at 1.
  unfold R.v3344, N.v3344.
  rewrite ?node_3343.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1413_nr_5F1416.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1413_nr_5F1416 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3345 (s : N.State) (i : N.Inputs) :
  R.v3345 (state s) (inputs i) = Zmod.unsigned (N.v3345 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3345 s i)) at 1.
  unfold R.v3345, N.v3345.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3346 (s : N.State) (i : N.Inputs) :
  R.v3346 (state s) (inputs i) = Zmod.unsigned (N.v3346 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3346 s i)) at 1.
  unfold R.v3346, N.v3346.
  rewrite ?node_3345.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1414_nr_5F1417.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1414_nr_5F1417 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3347 (s : N.State) (i : N.Inputs) :
  R.v3347 (state s) (inputs i) = Zmod.unsigned (N.v3347 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3347 s i)) at 1.
  unfold R.v3347, N.v3347.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3348 (s : N.State) (i : N.Inputs) :
  R.v3348 (state s) (inputs i) = Zmod.unsigned (N.v3348 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3348 s i)) at 1.
  unfold R.v3348, N.v3348.
  rewrite ?node_3347.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1415_nr_5F1418.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1415_nr_5F1418 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3349 (s : N.State) (i : N.Inputs) :
  R.v3349 (state s) (inputs i) = Zmod.unsigned (N.v3349 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3349 s i)) at 1.
  unfold R.v3349, N.v3349.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3350 (s : N.State) (i : N.Inputs) :
  R.v3350 (state s) (inputs i) = Zmod.unsigned (N.v3350 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3350 s i)) at 1.
  unfold R.v3350, N.v3350.
  rewrite ?node_3349.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1416_nr_5F1419.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1416_nr_5F1419 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3351 (s : N.State) (i : N.Inputs) :
  R.v3351 (state s) (inputs i) = Zmod.unsigned (N.v3351 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3351 s i)) at 1.
  unfold R.v3351, N.v3351.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3352 (s : N.State) (i : N.Inputs) :
  R.v3352 (state s) (inputs i) = Zmod.unsigned (N.v3352 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3352 s i)) at 1.
  unfold R.v3352, N.v3352.
  rewrite ?node_3351.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1417_nr_5F1420.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1417_nr_5F1420 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3353 (s : N.State) (i : N.Inputs) :
  R.v3353 (state s) (inputs i) = Zmod.unsigned (N.v3353 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3353 s i)) at 1.
  unfold R.v3353, N.v3353.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3354 (s : N.State) (i : N.Inputs) :
  R.v3354 (state s) (inputs i) = Zmod.unsigned (N.v3354 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3354 s i)) at 1.
  unfold R.v3354, N.v3354.
  rewrite ?node_3353.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1418_nr_5F1421.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1418_nr_5F1421 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3355 (s : N.State) (i : N.Inputs) :
  R.v3355 (state s) (inputs i) = Zmod.unsigned (N.v3355 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3355 s i)) at 1.
  unfold R.v3355, N.v3355.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3356 (s : N.State) (i : N.Inputs) :
  R.v3356 (state s) (inputs i) = Zmod.unsigned (N.v3356 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3356 s i)) at 1.
  unfold R.v3356, N.v3356.
  rewrite ?node_3355.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1419_nr_5F1422.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1419_nr_5F1422 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3357 (s : N.State) (i : N.Inputs) :
  R.v3357 (state s) (inputs i) = Zmod.unsigned (N.v3357 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3357 s i)) at 1.
  unfold R.v3357, N.v3357.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3358 (s : N.State) (i : N.Inputs) :
  R.v3358 (state s) (inputs i) = Zmod.unsigned (N.v3358 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3358 s i)) at 1.
  unfold R.v3358, N.v3358.
  rewrite ?node_3357.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1420_nr_5F1423.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1420_nr_5F1423 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3359 (s : N.State) (i : N.Inputs) :
  R.v3359 (state s) (inputs i) = Zmod.unsigned (N.v3359 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3359 s i)) at 1.
  unfold R.v3359, N.v3359.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3360 (s : N.State) (i : N.Inputs) :
  R.v3360 (state s) (inputs i) = Zmod.unsigned (N.v3360 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3360 s i)) at 1.
  unfold R.v3360, N.v3360.
  rewrite ?node_3359.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1421_nr_5F1424.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1421_nr_5F1424 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3361 (s : N.State) (i : N.Inputs) :
  R.v3361 (state s) (inputs i) = Zmod.unsigned (N.v3361 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3361 s i)) at 1.
  unfold R.v3361, N.v3361.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3362 (s : N.State) (i : N.Inputs) :
  R.v3362 (state s) (inputs i) = Zmod.unsigned (N.v3362 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3362 s i)) at 1.
  unfold R.v3362, N.v3362.
  rewrite ?node_3361.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1422_nr_5F1425.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1422_nr_5F1425 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3363 (s : N.State) (i : N.Inputs) :
  R.v3363 (state s) (inputs i) = Zmod.unsigned (N.v3363 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3363 s i)) at 1.
  unfold R.v3363, N.v3363.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3364 (s : N.State) (i : N.Inputs) :
  R.v3364 (state s) (inputs i) = Zmod.unsigned (N.v3364 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3364 s i)) at 1.
  unfold R.v3364, N.v3364.
  rewrite ?node_3363.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1423_nr_5F1426.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1423_nr_5F1426 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3365 (s : N.State) (i : N.Inputs) :
  R.v3365 (state s) (inputs i) = Zmod.unsigned (N.v3365 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3365 s i)) at 1.
  unfold R.v3365, N.v3365.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3366 (s : N.State) (i : N.Inputs) :
  R.v3366 (state s) (inputs i) = Zmod.unsigned (N.v3366 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3366 s i)) at 1.
  unfold R.v3366, N.v3366.
  rewrite ?node_3365.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1424_nr_5F1427.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1424_nr_5F1427 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3367 (s : N.State) (i : N.Inputs) :
  R.v3367 (state s) (inputs i) = Zmod.unsigned (N.v3367 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3367 s i)) at 1.
  unfold R.v3367, N.v3367.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3368 (s : N.State) (i : N.Inputs) :
  R.v3368 (state s) (inputs i) = Zmod.unsigned (N.v3368 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3368 s i)) at 1.
  unfold R.v3368, N.v3368.
  rewrite ?node_3367.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1425_nr_5F1428.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1425_nr_5F1428 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3369 (s : N.State) (i : N.Inputs) :
  R.v3369 (state s) (inputs i) = Zmod.unsigned (N.v3369 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3369 s i)) at 1.
  unfold R.v3369, N.v3369.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3370 (s : N.State) (i : N.Inputs) :
  R.v3370 (state s) (inputs i) = Zmod.unsigned (N.v3370 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3370 s i)) at 1.
  unfold R.v3370, N.v3370.
  rewrite ?node_3369.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1426_nr_5F1429.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1426_nr_5F1429 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3371 (s : N.State) (i : N.Inputs) :
  R.v3371 (state s) (inputs i) = Zmod.unsigned (N.v3371 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3371 s i)) at 1.
  unfold R.v3371, N.v3371.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3372 (s : N.State) (i : N.Inputs) :
  R.v3372 (state s) (inputs i) = Zmod.unsigned (N.v3372 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3372 s i)) at 1.
  unfold R.v3372, N.v3372.
  rewrite ?node_3371.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1427_nr_5F1430.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1427_nr_5F1430 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3373 (s : N.State) (i : N.Inputs) :
  R.v3373 (state s) (inputs i) = Zmod.unsigned (N.v3373 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3373 s i)) at 1.
  unfold R.v3373, N.v3373.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3374 (s : N.State) (i : N.Inputs) :
  R.v3374 (state s) (inputs i) = Zmod.unsigned (N.v3374 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3374 s i)) at 1.
  unfold R.v3374, N.v3374.
  rewrite ?node_3373.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1428_nr_5F1431.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1428_nr_5F1431 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3375 (s : N.State) (i : N.Inputs) :
  R.v3375 (state s) (inputs i) = Zmod.unsigned (N.v3375 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3375 s i)) at 1.
  unfold R.v3375, N.v3375.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3376 (s : N.State) (i : N.Inputs) :
  R.v3376 (state s) (inputs i) = Zmod.unsigned (N.v3376 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3376 s i)) at 1.
  unfold R.v3376, N.v3376.
  rewrite ?node_3375.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1429_nr_5F1432.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1429_nr_5F1432 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3377 (s : N.State) (i : N.Inputs) :
  R.v3377 (state s) (inputs i) = Zmod.unsigned (N.v3377 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3377 s i)) at 1.
  unfold R.v3377, N.v3377.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3378 (s : N.State) (i : N.Inputs) :
  R.v3378 (state s) (inputs i) = Zmod.unsigned (N.v3378 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3378 s i)) at 1.
  unfold R.v3378, N.v3378.
  rewrite ?node_3377.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1430_nr_5F1433.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1430_nr_5F1433 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3379 (s : N.State) (i : N.Inputs) :
  R.v3379 (state s) (inputs i) = Zmod.unsigned (N.v3379 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3379 s i)) at 1.
  unfold R.v3379, N.v3379.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3380 (s : N.State) (i : N.Inputs) :
  R.v3380 (state s) (inputs i) = Zmod.unsigned (N.v3380 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3380 s i)) at 1.
  unfold R.v3380, N.v3380.
  rewrite ?node_3379.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1431_nr_5F1434.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1431_nr_5F1434 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3381 (s : N.State) (i : N.Inputs) :
  R.v3381 (state s) (inputs i) = Zmod.unsigned (N.v3381 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3381 s i)) at 1.
  unfold R.v3381, N.v3381.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3382 (s : N.State) (i : N.Inputs) :
  R.v3382 (state s) (inputs i) = Zmod.unsigned (N.v3382 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3382 s i)) at 1.
  unfold R.v3382, N.v3382.
  rewrite ?node_3381.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1432_nr_5F1435.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1432_nr_5F1435 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3383 (s : N.State) (i : N.Inputs) :
  R.v3383 (state s) (inputs i) = Zmod.unsigned (N.v3383 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3383 s i)) at 1.
  unfold R.v3383, N.v3383.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3384 (s : N.State) (i : N.Inputs) :
  R.v3384 (state s) (inputs i) = Zmod.unsigned (N.v3384 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3384 s i)) at 1.
  unfold R.v3384, N.v3384.
  rewrite ?node_3383.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1433_nr_5F1436.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1433_nr_5F1436 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3385 (s : N.State) (i : N.Inputs) :
  R.v3385 (state s) (inputs i) = Zmod.unsigned (N.v3385 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3385 s i)) at 1.
  unfold R.v3385, N.v3385.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3386 (s : N.State) (i : N.Inputs) :
  R.v3386 (state s) (inputs i) = Zmod.unsigned (N.v3386 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3386 s i)) at 1.
  unfold R.v3386, N.v3386.
  rewrite ?node_3385.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1434_nr_5F1437.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1434_nr_5F1437 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3387 (s : N.State) (i : N.Inputs) :
  R.v3387 (state s) (inputs i) = Zmod.unsigned (N.v3387 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3387 s i)) at 1.
  unfold R.v3387, N.v3387.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3388 (s : N.State) (i : N.Inputs) :
  R.v3388 (state s) (inputs i) = Zmod.unsigned (N.v3388 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3388 s i)) at 1.
  unfold R.v3388, N.v3388.
  rewrite ?node_3387.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1435_nr_5F1438.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1435_nr_5F1438 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3389 (s : N.State) (i : N.Inputs) :
  R.v3389 (state s) (inputs i) = Zmod.unsigned (N.v3389 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3389 s i)) at 1.
  unfold R.v3389, N.v3389.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3390 (s : N.State) (i : N.Inputs) :
  R.v3390 (state s) (inputs i) = Zmod.unsigned (N.v3390 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3390 s i)) at 1.
  unfold R.v3390, N.v3390.
  rewrite ?node_3389.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1436_nr_5F1439.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1436_nr_5F1439 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3391 (s : N.State) (i : N.Inputs) :
  R.v3391 (state s) (inputs i) = Zmod.unsigned (N.v3391 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3391 s i)) at 1.
  unfold R.v3391, N.v3391.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3392 (s : N.State) (i : N.Inputs) :
  R.v3392 (state s) (inputs i) = Zmod.unsigned (N.v3392 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3392 s i)) at 1.
  unfold R.v3392, N.v3392.
  rewrite ?node_3391.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1437_nr_5F1440.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1437_nr_5F1440 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3393 (s : N.State) (i : N.Inputs) :
  R.v3393 (state s) (inputs i) = Zmod.unsigned (N.v3393 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3393 s i)) at 1.
  unfold R.v3393, N.v3393.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3394 (s : N.State) (i : N.Inputs) :
  R.v3394 (state s) (inputs i) = Zmod.unsigned (N.v3394 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3394 s i)) at 1.
  unfold R.v3394, N.v3394.
  unfold R.v3021, N.v3021.
  rewrite ?node_3393.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3395 (s : N.State) (i : N.Inputs) :
  R.v3395 (state s) (inputs i) = Zmod.unsigned (N.v3395 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3395 s i)) at 1.
  unfold R.v3395, N.v3395.
  rewrite ?node_3394.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1438_nr_5F1441.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1438_nr_5F1441 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3396 (s : N.State) (i : N.Inputs) :
  R.v3396 (state s) (inputs i) = Zmod.unsigned (N.v3396 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3396 s i)) at 1.
  unfold R.v3396, N.v3396.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3397 (s : N.State) (i : N.Inputs) :
  R.v3397 (state s) (inputs i) = Zmod.unsigned (N.v3397 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3397 s i)) at 1.
  unfold R.v3397, N.v3397.
  rewrite ?node_3396.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1439_nr_5F1442.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1439_nr_5F1442 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3398 (s : N.State) (i : N.Inputs) :
  R.v3398 (state s) (inputs i) = Zmod.unsigned (N.v3398 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3398 s i)) at 1.
  unfold R.v3398, N.v3398.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3399 (s : N.State) (i : N.Inputs) :
  R.v3399 (state s) (inputs i) = Zmod.unsigned (N.v3399 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3399 s i)) at 1.
  unfold R.v3399, N.v3399.
  rewrite ?node_3398.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1440_nr_5F1443.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1440_nr_5F1443 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3400 (s : N.State) (i : N.Inputs) :
  R.v3400 (state s) (inputs i) = Zmod.unsigned (N.v3400 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3400 s i)) at 1.
  unfold R.v3400, N.v3400.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3401 (s : N.State) (i : N.Inputs) :
  R.v3401 (state s) (inputs i) = Zmod.unsigned (N.v3401 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3401 s i)) at 1.
  unfold R.v3401, N.v3401.
  rewrite ?node_3400.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1441_nr_5F1444.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1441_nr_5F1444 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3402 (s : N.State) (i : N.Inputs) :
  R.v3402 (state s) (inputs i) = Zmod.unsigned (N.v3402 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3402 s i)) at 1.
  unfold R.v3402, N.v3402.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3403 (s : N.State) (i : N.Inputs) :
  R.v3403 (state s) (inputs i) = Zmod.unsigned (N.v3403 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3403 s i)) at 1.
  unfold R.v3403, N.v3403.
  rewrite ?node_3402.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1442_nr_5F1445.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1442_nr_5F1445 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3404 (s : N.State) (i : N.Inputs) :
  R.v3404 (state s) (inputs i) = Zmod.unsigned (N.v3404 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3404 s i)) at 1.
  unfold R.v3404, N.v3404.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3405 (s : N.State) (i : N.Inputs) :
  R.v3405 (state s) (inputs i) = Zmod.unsigned (N.v3405 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3405 s i)) at 1.
  unfold R.v3405, N.v3405.
  rewrite ?node_3404.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1443_nr_5F1446.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1443_nr_5F1446 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3406 (s : N.State) (i : N.Inputs) :
  R.v3406 (state s) (inputs i) = Zmod.unsigned (N.v3406 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3406 s i)) at 1.
  unfold R.v3406, N.v3406.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3407 (s : N.State) (i : N.Inputs) :
  R.v3407 (state s) (inputs i) = Zmod.unsigned (N.v3407 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3407 s i)) at 1.
  unfold R.v3407, N.v3407.
  rewrite ?node_3406.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1444_nr_5F1447.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1444_nr_5F1447 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3408 (s : N.State) (i : N.Inputs) :
  R.v3408 (state s) (inputs i) = Zmod.unsigned (N.v3408 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3408 s i)) at 1.
  unfold R.v3408, N.v3408.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3409 (s : N.State) (i : N.Inputs) :
  R.v3409 (state s) (inputs i) = Zmod.unsigned (N.v3409 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3409 s i)) at 1.
  unfold R.v3409, N.v3409.
  rewrite ?node_3408.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1445_nr_5F1448.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1445_nr_5F1448 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3410 (s : N.State) (i : N.Inputs) :
  R.v3410 (state s) (inputs i) = Zmod.unsigned (N.v3410 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3410 s i)) at 1.
  unfold R.v3410, N.v3410.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3411 (s : N.State) (i : N.Inputs) :
  R.v3411 (state s) (inputs i) = Zmod.unsigned (N.v3411 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3411 s i)) at 1.
  unfold R.v3411, N.v3411.
  rewrite ?node_3410.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1446_nr_5F1449.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1446_nr_5F1449 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3412 (s : N.State) (i : N.Inputs) :
  R.v3412 (state s) (inputs i) = Zmod.unsigned (N.v3412 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3412 s i)) at 1.
  unfold R.v3412, N.v3412.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3413 (s : N.State) (i : N.Inputs) :
  R.v3413 (state s) (inputs i) = Zmod.unsigned (N.v3413 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3413 s i)) at 1.
  unfold R.v3413, N.v3413.
  rewrite ?node_3412.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1447_nr_5F1450.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1447_nr_5F1450 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3414 (s : N.State) (i : N.Inputs) :
  R.v3414 (state s) (inputs i) = Zmod.unsigned (N.v3414 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3414 s i)) at 1.
  unfold R.v3414, N.v3414.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3415 (s : N.State) (i : N.Inputs) :
  R.v3415 (state s) (inputs i) = Zmod.unsigned (N.v3415 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3415 s i)) at 1.
  unfold R.v3415, N.v3415.
  rewrite ?node_3414.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1448_nr_5F1451.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1448_nr_5F1451 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3416 (s : N.State) (i : N.Inputs) :
  R.v3416 (state s) (inputs i) = Zmod.unsigned (N.v3416 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3416 s i)) at 1.
  unfold R.v3416, N.v3416.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3417 (s : N.State) (i : N.Inputs) :
  R.v3417 (state s) (inputs i) = Zmod.unsigned (N.v3417 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3417 s i)) at 1.
  unfold R.v3417, N.v3417.
  rewrite ?node_3416.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1449_nr_5F1452.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1449_nr_5F1452 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3418 (s : N.State) (i : N.Inputs) :
  R.v3418 (state s) (inputs i) = Zmod.unsigned (N.v3418 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3418 s i)) at 1.
  unfold R.v3418, N.v3418.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3419 (s : N.State) (i : N.Inputs) :
  R.v3419 (state s) (inputs i) = Zmod.unsigned (N.v3419 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3419 s i)) at 1.
  unfold R.v3419, N.v3419.
  rewrite ?node_3418.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1450_nr_5F1453.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1450_nr_5F1453 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3420 (s : N.State) (i : N.Inputs) :
  R.v3420 (state s) (inputs i) = Zmod.unsigned (N.v3420 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3420 s i)) at 1.
  unfold R.v3420, N.v3420.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3421 (s : N.State) (i : N.Inputs) :
  R.v3421 (state s) (inputs i) = Zmod.unsigned (N.v3421 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3421 s i)) at 1.
  unfold R.v3421, N.v3421.
  rewrite ?node_3420.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1451_nr_5F1454.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1451_nr_5F1454 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3422 (s : N.State) (i : N.Inputs) :
  R.v3422 (state s) (inputs i) = Zmod.unsigned (N.v3422 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3422 s i)) at 1.
  unfold R.v3422, N.v3422.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3423 (s : N.State) (i : N.Inputs) :
  R.v3423 (state s) (inputs i) = Zmod.unsigned (N.v3423 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3423 s i)) at 1.
  unfold R.v3423, N.v3423.
  rewrite ?node_3422.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1452_nr_5F1455.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1452_nr_5F1455 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3424 (s : N.State) (i : N.Inputs) :
  R.v3424 (state s) (inputs i) = Zmod.unsigned (N.v3424 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3424 s i)) at 1.
  unfold R.v3424, N.v3424.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3425 (s : N.State) (i : N.Inputs) :
  R.v3425 (state s) (inputs i) = Zmod.unsigned (N.v3425 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3425 s i)) at 1.
  unfold R.v3425, N.v3425.
  rewrite ?node_3424.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1453_nr_5F1456.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1453_nr_5F1456 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3426 (s : N.State) (i : N.Inputs) :
  R.v3426 (state s) (inputs i) = Zmod.unsigned (N.v3426 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3426 s i)) at 1.
  unfold R.v3426, N.v3426.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3427 (s : N.State) (i : N.Inputs) :
  R.v3427 (state s) (inputs i) = Zmod.unsigned (N.v3427 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3427 s i)) at 1.
  unfold R.v3427, N.v3427.
  rewrite ?node_3426.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1454_nr_5F1457.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1454_nr_5F1457 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3428 (s : N.State) (i : N.Inputs) :
  R.v3428 (state s) (inputs i) = Zmod.unsigned (N.v3428 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3428 s i)) at 1.
  unfold R.v3428, N.v3428.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3429 (s : N.State) (i : N.Inputs) :
  R.v3429 (state s) (inputs i) = Zmod.unsigned (N.v3429 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3429 s i)) at 1.
  unfold R.v3429, N.v3429.
  rewrite ?node_3428.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1455_nr_5F1458.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1455_nr_5F1458 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3430 (s : N.State) (i : N.Inputs) :
  R.v3430 (state s) (inputs i) = Zmod.unsigned (N.v3430 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3430 s i)) at 1.
  unfold R.v3430, N.v3430.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3431 (s : N.State) (i : N.Inputs) :
  R.v3431 (state s) (inputs i) = Zmod.unsigned (N.v3431 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3431 s i)) at 1.
  unfold R.v3431, N.v3431.
  rewrite ?node_3430.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1456_nr_5F1459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1456_nr_5F1459 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3432 (s : N.State) (i : N.Inputs) :
  R.v3432 (state s) (inputs i) = Zmod.unsigned (N.v3432 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3432 s i)) at 1.
  unfold R.v3432, N.v3432.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3433 (s : N.State) (i : N.Inputs) :
  R.v3433 (state s) (inputs i) = Zmod.unsigned (N.v3433 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3433 s i)) at 1.
  unfold R.v3433, N.v3433.
  rewrite ?node_3432.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1457_nr_5F1460.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1457_nr_5F1460 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3434 (s : N.State) (i : N.Inputs) :
  R.v3434 (state s) (inputs i) = Zmod.unsigned (N.v3434 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3434 s i)) at 1.
  unfold R.v3434, N.v3434.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3435 (s : N.State) (i : N.Inputs) :
  R.v3435 (state s) (inputs i) = Zmod.unsigned (N.v3435 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3435 s i)) at 1.
  unfold R.v3435, N.v3435.
  rewrite ?node_3434.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1458_nr_5F1461.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1458_nr_5F1461 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3436 (s : N.State) (i : N.Inputs) :
  R.v3436 (state s) (inputs i) = Zmod.unsigned (N.v3436 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3436 s i)) at 1.
  unfold R.v3436, N.v3436.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3437 (s : N.State) (i : N.Inputs) :
  R.v3437 (state s) (inputs i) = Zmod.unsigned (N.v3437 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3437 s i)) at 1.
  unfold R.v3437, N.v3437.
  rewrite ?node_3436.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1459_nr_5F1462.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1459_nr_5F1462 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3438 (s : N.State) (i : N.Inputs) :
  R.v3438 (state s) (inputs i) = Zmod.unsigned (N.v3438 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3438 s i)) at 1.
  unfold R.v3438, N.v3438.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3439 (s : N.State) (i : N.Inputs) :
  R.v3439 (state s) (inputs i) = Zmod.unsigned (N.v3439 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3439 s i)) at 1.
  unfold R.v3439, N.v3439.
  rewrite ?node_3438.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1460_nr_5F1463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1460_nr_5F1463 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3440 (s : N.State) (i : N.Inputs) :
  R.v3440 (state s) (inputs i) = Zmod.unsigned (N.v3440 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3440 s i)) at 1.
  unfold R.v3440, N.v3440.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3441 (s : N.State) (i : N.Inputs) :
  R.v3441 (state s) (inputs i) = Zmod.unsigned (N.v3441 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3441 s i)) at 1.
  unfold R.v3441, N.v3441.
  rewrite ?node_3440.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1461_nr_5F1464.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1461_nr_5F1464 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3442 (s : N.State) (i : N.Inputs) :
  R.v3442 (state s) (inputs i) = Zmod.unsigned (N.v3442 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3442 s i)) at 1.
  unfold R.v3442, N.v3442.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3443 (s : N.State) (i : N.Inputs) :
  R.v3443 (state s) (inputs i) = Zmod.unsigned (N.v3443 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3443 s i)) at 1.
  unfold R.v3443, N.v3443.
  rewrite ?node_3442.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1462_nr_5F1465.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1462_nr_5F1465 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3444 (s : N.State) (i : N.Inputs) :
  R.v3444 (state s) (inputs i) = Zmod.unsigned (N.v3444 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3444 s i)) at 1.
  unfold R.v3444, N.v3444.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3445 (s : N.State) (i : N.Inputs) :
  R.v3445 (state s) (inputs i) = Zmod.unsigned (N.v3445 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3445 s i)) at 1.
  unfold R.v3445, N.v3445.
  rewrite ?node_3444.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1463_nr_5F1466.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1463_nr_5F1466 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3446 (s : N.State) (i : N.Inputs) :
  R.v3446 (state s) (inputs i) = Zmod.unsigned (N.v3446 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3446 s i)) at 1.
  unfold R.v3446, N.v3446.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3447 (s : N.State) (i : N.Inputs) :
  R.v3447 (state s) (inputs i) = Zmod.unsigned (N.v3447 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3447 s i)) at 1.
  unfold R.v3447, N.v3447.
  rewrite ?node_3446.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1464_nr_5F1467.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1464_nr_5F1467 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3448 (s : N.State) (i : N.Inputs) :
  R.v3448 (state s) (inputs i) = Zmod.unsigned (N.v3448 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3448 s i)) at 1.
  unfold R.v3448, N.v3448.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3449 (s : N.State) (i : N.Inputs) :
  R.v3449 (state s) (inputs i) = Zmod.unsigned (N.v3449 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3449 s i)) at 1.
  unfold R.v3449, N.v3449.
  rewrite ?node_3448.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1465_nr_5F1468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1465_nr_5F1468 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3450 (s : N.State) (i : N.Inputs) :
  R.v3450 (state s) (inputs i) = Zmod.unsigned (N.v3450 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3450 s i)) at 1.
  unfold R.v3450, N.v3450.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3451 (s : N.State) (i : N.Inputs) :
  R.v3451 (state s) (inputs i) = Zmod.unsigned (N.v3451 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3451 s i)) at 1.
  unfold R.v3451, N.v3451.
  rewrite ?node_3450.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1466_nr_5F1469.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1466_nr_5F1469 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3452 (s : N.State) (i : N.Inputs) :
  R.v3452 (state s) (inputs i) = Zmod.unsigned (N.v3452 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3452 s i)) at 1.
  unfold R.v3452, N.v3452.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3453 (s : N.State) (i : N.Inputs) :
  R.v3453 (state s) (inputs i) = Zmod.unsigned (N.v3453 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3453 s i)) at 1.
  unfold R.v3453, N.v3453.
  rewrite ?node_3452.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1467_nr_5F1471.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1467_nr_5F1471 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3454 (s : N.State) (i : N.Inputs) :
  R.v3454 (state s) (inputs i) = Zmod.unsigned (N.v3454 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3454 s i)) at 1.
  unfold R.v3454, N.v3454.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3455 (s : N.State) (i : N.Inputs) :
  R.v3455 (state s) (inputs i) = Zmod.unsigned (N.v3455 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3455 s i)) at 1.
  unfold R.v3455, N.v3455.
  rewrite ?node_3454.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1468_nr_5F1472.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1468_nr_5F1472 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3456 (s : N.State) (i : N.Inputs) :
  R.v3456 (state s) (inputs i) = Zmod.unsigned (N.v3456 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3456 s i)) at 1.
  unfold R.v3456, N.v3456.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3457 (s : N.State) (i : N.Inputs) :
  R.v3457 (state s) (inputs i) = Zmod.unsigned (N.v3457 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3457 s i)) at 1.
  unfold R.v3457, N.v3457.
  rewrite ?node_3456.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1469_nr_5F1473.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1469_nr_5F1473 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3458 (s : N.State) (i : N.Inputs) :
  R.v3458 (state s) (inputs i) = Zmod.unsigned (N.v3458 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3458 s i)) at 1.
  unfold R.v3458, N.v3458.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3459 (s : N.State) (i : N.Inputs) :
  R.v3459 (state s) (inputs i) = Zmod.unsigned (N.v3459 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3459 s i)) at 1.
  unfold R.v3459, N.v3459.
  rewrite ?node_3458.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1470_nr_5F1474.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1470_nr_5F1474 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3460 (s : N.State) (i : N.Inputs) :
  R.v3460 (state s) (inputs i) = Zmod.unsigned (N.v3460 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3460 s i)) at 1.
  unfold R.v3460, N.v3460.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3461 (s : N.State) (i : N.Inputs) :
  R.v3461 (state s) (inputs i) = Zmod.unsigned (N.v3461 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3461 s i)) at 1.
  unfold R.v3461, N.v3461.
  rewrite ?node_3460.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1471_nr_5F1475.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1471_nr_5F1475 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3462 (s : N.State) (i : N.Inputs) :
  R.v3462 (state s) (inputs i) = Zmod.unsigned (N.v3462 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3462 s i)) at 1.
  unfold R.v3462, N.v3462.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3463 (s : N.State) (i : N.Inputs) :
  R.v3463 (state s) (inputs i) = Zmod.unsigned (N.v3463 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3463 s i)) at 1.
  unfold R.v3463, N.v3463.
  rewrite ?node_3462.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1472_nr_5F1476.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1472_nr_5F1476 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3464 (s : N.State) (i : N.Inputs) :
  R.v3464 (state s) (inputs i) = Zmod.unsigned (N.v3464 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3464 s i)) at 1.
  unfold R.v3464, N.v3464.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3465 (s : N.State) (i : N.Inputs) :
  R.v3465 (state s) (inputs i) = Zmod.unsigned (N.v3465 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3465 s i)) at 1.
  unfold R.v3465, N.v3465.
  rewrite ?node_3464.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1473_nr_5F1477.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1473_nr_5F1477 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3466 (s : N.State) (i : N.Inputs) :
  R.v3466 (state s) (inputs i) = Zmod.unsigned (N.v3466 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3466 s i)) at 1.
  unfold R.v3466, N.v3466.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3467 (s : N.State) (i : N.Inputs) :
  R.v3467 (state s) (inputs i) = Zmod.unsigned (N.v3467 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3467 s i)) at 1.
  unfold R.v3467, N.v3467.
  rewrite ?node_3466.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1474_nr_5F1478.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1474_nr_5F1478 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3468 (s : N.State) (i : N.Inputs) :
  R.v3468 (state s) (inputs i) = Zmod.unsigned (N.v3468 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3468 s i)) at 1.
  unfold R.v3468, N.v3468.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3469 (s : N.State) (i : N.Inputs) :
  R.v3469 (state s) (inputs i) = Zmod.unsigned (N.v3469 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3469 s i)) at 1.
  unfold R.v3469, N.v3469.
  rewrite ?node_3468.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1475_nr_5F1479.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1475_nr_5F1479 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3470 (s : N.State) (i : N.Inputs) :
  R.v3470 (state s) (inputs i) = Zmod.unsigned (N.v3470 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3470 s i)) at 1.
  unfold R.v3470, N.v3470.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3471 (s : N.State) (i : N.Inputs) :
  R.v3471 (state s) (inputs i) = Zmod.unsigned (N.v3471 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3471 s i)) at 1.
  unfold R.v3471, N.v3471.
  rewrite ?node_3470.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1476_nr_5F1480.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1476_nr_5F1480 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3472 (s : N.State) (i : N.Inputs) :
  R.v3472 (state s) (inputs i) = Zmod.unsigned (N.v3472 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3472 s i)) at 1.
  unfold R.v3472, N.v3472.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3473 (s : N.State) (i : N.Inputs) :
  R.v3473 (state s) (inputs i) = Zmod.unsigned (N.v3473 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3473 s i)) at 1.
  unfold R.v3473, N.v3473.
  rewrite ?node_3472.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1477_nr_5F1481.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1477_nr_5F1481 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3474 (s : N.State) (i : N.Inputs) :
  R.v3474 (state s) (inputs i) = Zmod.unsigned (N.v3474 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3474 s i)) at 1.
  unfold R.v3474, N.v3474.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3475 (s : N.State) (i : N.Inputs) :
  R.v3475 (state s) (inputs i) = Zmod.unsigned (N.v3475 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3475 s i)) at 1.
  unfold R.v3475, N.v3475.
  rewrite ?node_3474.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1478_nr_5F1482.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1478_nr_5F1482 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3476 (s : N.State) (i : N.Inputs) :
  R.v3476 (state s) (inputs i) = Zmod.unsigned (N.v3476 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3476 s i)) at 1.
  unfold R.v3476, N.v3476.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3477 (s : N.State) (i : N.Inputs) :
  R.v3477 (state s) (inputs i) = Zmod.unsigned (N.v3477 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3477 s i)) at 1.
  unfold R.v3477, N.v3477.
  rewrite ?node_3476.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1479_nr_5F1483.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1479_nr_5F1483 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3478 (s : N.State) (i : N.Inputs) :
  R.v3478 (state s) (inputs i) = Zmod.unsigned (N.v3478 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3478 s i)) at 1.
  unfold R.v3478, N.v3478.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3479 (s : N.State) (i : N.Inputs) :
  R.v3479 (state s) (inputs i) = Zmod.unsigned (N.v3479 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3479 s i)) at 1.
  unfold R.v3479, N.v3479.
  rewrite ?node_3478.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1480_nr_5F1484.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1480_nr_5F1484 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3480 (s : N.State) (i : N.Inputs) :
  R.v3480 (state s) (inputs i) = Zmod.unsigned (N.v3480 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3480 s i)) at 1.
  unfold R.v3480, N.v3480.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3481 (s : N.State) (i : N.Inputs) :
  R.v3481 (state s) (inputs i) = Zmod.unsigned (N.v3481 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3481 s i)) at 1.
  unfold R.v3481, N.v3481.
  rewrite ?node_3480.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1481_nr_5F1485.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1481_nr_5F1485 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3482 (s : N.State) (i : N.Inputs) :
  R.v3482 (state s) (inputs i) = Zmod.unsigned (N.v3482 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3482 s i)) at 1.
  unfold R.v3482, N.v3482.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3483 (s : N.State) (i : N.Inputs) :
  R.v3483 (state s) (inputs i) = Zmod.unsigned (N.v3483 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3483 s i)) at 1.
  unfold R.v3483, N.v3483.
  rewrite ?node_3482.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1482_nr_5F1486.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1482_nr_5F1486 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3484 (s : N.State) (i : N.Inputs) :
  R.v3484 (state s) (inputs i) = Zmod.unsigned (N.v3484 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3484 s i)) at 1.
  unfold R.v3484, N.v3484.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3485 (s : N.State) (i : N.Inputs) :
  R.v3485 (state s) (inputs i) = Zmod.unsigned (N.v3485 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3485 s i)) at 1.
  unfold R.v3485, N.v3485.
  rewrite ?node_3484.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1483_nr_5F1487.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1483_nr_5F1487 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3486 (s : N.State) (i : N.Inputs) :
  R.v3486 (state s) (inputs i) = Zmod.unsigned (N.v3486 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3486 s i)) at 1.
  unfold R.v3486, N.v3486.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3487 (s : N.State) (i : N.Inputs) :
  R.v3487 (state s) (inputs i) = Zmod.unsigned (N.v3487 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3487 s i)) at 1.
  unfold R.v3487, N.v3487.
  rewrite ?node_3486.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1484_nr_5F1488.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1484_nr_5F1488 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3488 (s : N.State) (i : N.Inputs) :
  R.v3488 (state s) (inputs i) = Zmod.unsigned (N.v3488 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3488 s i)) at 1.
  unfold R.v3488, N.v3488.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3489 (s : N.State) (i : N.Inputs) :
  R.v3489 (state s) (inputs i) = Zmod.unsigned (N.v3489 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3489 s i)) at 1.
  unfold R.v3489, N.v3489.
  rewrite ?node_3488.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1485_nr_5F1489.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1485_nr_5F1489 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3490 (s : N.State) (i : N.Inputs) :
  R.v3490 (state s) (inputs i) = Zmod.unsigned (N.v3490 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3490 s i)) at 1.
  unfold R.v3490, N.v3490.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3491 (s : N.State) (i : N.Inputs) :
  R.v3491 (state s) (inputs i) = Zmod.unsigned (N.v3491 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3491 s i)) at 1.
  unfold R.v3491, N.v3491.
  rewrite ?node_3490.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1486_nr_5F1490.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1486_nr_5F1490 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3492 (s : N.State) (i : N.Inputs) :
  R.v3492 (state s) (inputs i) = Zmod.unsigned (N.v3492 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3492 s i)) at 1.
  unfold R.v3492, N.v3492.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3493 (s : N.State) (i : N.Inputs) :
  R.v3493 (state s) (inputs i) = Zmod.unsigned (N.v3493 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3493 s i)) at 1.
  unfold R.v3493, N.v3493.
  rewrite ?node_3492.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1487_nr_5F1491.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1487_nr_5F1491 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3494 (s : N.State) (i : N.Inputs) :
  R.v3494 (state s) (inputs i) = Zmod.unsigned (N.v3494 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3494 s i)) at 1.
  unfold R.v3494, N.v3494.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3495 (s : N.State) (i : N.Inputs) :
  R.v3495 (state s) (inputs i) = Zmod.unsigned (N.v3495 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3495 s i)) at 1.
  unfold R.v3495, N.v3495.
  rewrite ?node_3494.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1488_nr_5F1492.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1488_nr_5F1492 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3496 (s : N.State) (i : N.Inputs) :
  R.v3496 (state s) (inputs i) = Zmod.unsigned (N.v3496 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3496 s i)) at 1.
  unfold R.v3496, N.v3496.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3497 (s : N.State) (i : N.Inputs) :
  R.v3497 (state s) (inputs i) = Zmod.unsigned (N.v3497 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3497 s i)) at 1.
  unfold R.v3497, N.v3497.
  rewrite ?node_3496.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1489_nr_5F1493.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1489_nr_5F1493 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3498 (s : N.State) (i : N.Inputs) :
  R.v3498 (state s) (inputs i) = Zmod.unsigned (N.v3498 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3498 s i)) at 1.
  unfold R.v3498, N.v3498.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3499 (s : N.State) (i : N.Inputs) :
  R.v3499 (state s) (inputs i) = Zmod.unsigned (N.v3499 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3499 s i)) at 1.
  unfold R.v3499, N.v3499.
  rewrite ?node_3498.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1490_nr_5F1494.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1490_nr_5F1494 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3500 (s : N.State) (i : N.Inputs) :
  R.v3500 (state s) (inputs i) = Zmod.unsigned (N.v3500 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3500 s i)) at 1.
  unfold R.v3500, N.v3500.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3501 (s : N.State) (i : N.Inputs) :
  R.v3501 (state s) (inputs i) = Zmod.unsigned (N.v3501 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3501 s i)) at 1.
  unfold R.v3501, N.v3501.
  rewrite ?node_3500.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1491_nr_5F1495.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1491_nr_5F1495 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3502 (s : N.State) (i : N.Inputs) :
  R.v3502 (state s) (inputs i) = Zmod.unsigned (N.v3502 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3502 s i)) at 1.
  unfold R.v3502, N.v3502.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3503 (s : N.State) (i : N.Inputs) :
  R.v3503 (state s) (inputs i) = Zmod.unsigned (N.v3503 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3503 s i)) at 1.
  unfold R.v3503, N.v3503.
  rewrite ?node_3502.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1492_nr_5F1496.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1492_nr_5F1496 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3504 (s : N.State) (i : N.Inputs) :
  R.v3504 (state s) (inputs i) = Zmod.unsigned (N.v3504 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3504 s i)) at 1.
  unfold R.v3504, N.v3504.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3505 (s : N.State) (i : N.Inputs) :
  R.v3505 (state s) (inputs i) = Zmod.unsigned (N.v3505 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3505 s i)) at 1.
  unfold R.v3505, N.v3505.
  rewrite ?node_3504.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1493_nr_5F1497.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1493_nr_5F1497 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3506 (s : N.State) (i : N.Inputs) :
  R.v3506 (state s) (inputs i) = Zmod.unsigned (N.v3506 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3506 s i)) at 1.
  unfold R.v3506, N.v3506.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3507 (s : N.State) (i : N.Inputs) :
  R.v3507 (state s) (inputs i) = Zmod.unsigned (N.v3507 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3507 s i)) at 1.
  unfold R.v3507, N.v3507.
  rewrite ?node_3506.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1494_nr_5F1498.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1494_nr_5F1498 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3508 (s : N.State) (i : N.Inputs) :
  R.v3508 (state s) (inputs i) = Zmod.unsigned (N.v3508 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3508 s i)) at 1.
  unfold R.v3508, N.v3508.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3509 (s : N.State) (i : N.Inputs) :
  R.v3509 (state s) (inputs i) = Zmod.unsigned (N.v3509 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3509 s i)) at 1.
  unfold R.v3509, N.v3509.
  unfold R.v3021, N.v3021.
  rewrite ?node_3508.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3510 (s : N.State) (i : N.Inputs) :
  R.v3510 (state s) (inputs i) = Zmod.unsigned (N.v3510 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3510 s i)) at 1.
  unfold R.v3510, N.v3510.
  rewrite ?node_3509.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1495_nr_5F1499.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1495_nr_5F1499 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3511 (s : N.State) (i : N.Inputs) :
  R.v3511 (state s) (inputs i) = Zmod.unsigned (N.v3511 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3511 s i)) at 1.
  unfold R.v3511, N.v3511.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3512 (s : N.State) (i : N.Inputs) :
  R.v3512 (state s) (inputs i) = Zmod.unsigned (N.v3512 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3512 s i)) at 1.
  unfold R.v3512, N.v3512.
  rewrite ?node_3511.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1496_nr_5F1500.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1496_nr_5F1500 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3513 (s : N.State) (i : N.Inputs) :
  R.v3513 (state s) (inputs i) = Zmod.unsigned (N.v3513 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3513 s i)) at 1.
  unfold R.v3513, N.v3513.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3514 (s : N.State) (i : N.Inputs) :
  R.v3514 (state s) (inputs i) = Zmod.unsigned (N.v3514 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3514 s i)) at 1.
  unfold R.v3514, N.v3514.
  rewrite ?node_3513.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1497_nr_5F1501.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1497_nr_5F1501 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3515 (s : N.State) (i : N.Inputs) :
  R.v3515 (state s) (inputs i) = Zmod.unsigned (N.v3515 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3515 s i)) at 1.
  unfold R.v3515, N.v3515.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3516 (s : N.State) (i : N.Inputs) :
  R.v3516 (state s) (inputs i) = Zmod.unsigned (N.v3516 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3516 s i)) at 1.
  unfold R.v3516, N.v3516.
  rewrite ?node_3515.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1498_nr_5F1502.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1498_nr_5F1502 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3517 (s : N.State) (i : N.Inputs) :
  R.v3517 (state s) (inputs i) = Zmod.unsigned (N.v3517 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3517 s i)) at 1.
  unfold R.v3517, N.v3517.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3518 (s : N.State) (i : N.Inputs) :
  R.v3518 (state s) (inputs i) = Zmod.unsigned (N.v3518 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3518 s i)) at 1.
  unfold R.v3518, N.v3518.
  rewrite ?node_3517.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1499_nr_5F1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1499_nr_5F1503 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3519 (s : N.State) (i : N.Inputs) :
  R.v3519 (state s) (inputs i) = Zmod.unsigned (N.v3519 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3519 s i)) at 1.
  unfold R.v3519, N.v3519.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3520 (s : N.State) (i : N.Inputs) :
  R.v3520 (state s) (inputs i) = Zmod.unsigned (N.v3520 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3520 s i)) at 1.
  unfold R.v3520, N.v3520.
  rewrite ?node_3519.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1500_nr_5F1504.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1500_nr_5F1504 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3521 (s : N.State) (i : N.Inputs) :
  R.v3521 (state s) (inputs i) = Zmod.unsigned (N.v3521 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3521 s i)) at 1.
  unfold R.v3521, N.v3521.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3522 (s : N.State) (i : N.Inputs) :
  R.v3522 (state s) (inputs i) = Zmod.unsigned (N.v3522 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3522 s i)) at 1.
  unfold R.v3522, N.v3522.
  rewrite ?node_3521.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1501_nr_5F1505.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1501_nr_5F1505 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3523 (s : N.State) (i : N.Inputs) :
  R.v3523 (state s) (inputs i) = Zmod.unsigned (N.v3523 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3523 s i)) at 1.
  unfold R.v3523, N.v3523.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3524 (s : N.State) (i : N.Inputs) :
  R.v3524 (state s) (inputs i) = Zmod.unsigned (N.v3524 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3524 s i)) at 1.
  unfold R.v3524, N.v3524.
  rewrite ?node_3523.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1502_nr_5F1506.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1502_nr_5F1506 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3525 (s : N.State) (i : N.Inputs) :
  R.v3525 (state s) (inputs i) = Zmod.unsigned (N.v3525 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3525 s i)) at 1.
  unfold R.v3525, N.v3525.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3526 (s : N.State) (i : N.Inputs) :
  R.v3526 (state s) (inputs i) = Zmod.unsigned (N.v3526 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3526 s i)) at 1.
  unfold R.v3526, N.v3526.
  rewrite ?node_3525.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1503_nr_5F1507.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1503_nr_5F1507 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3527 (s : N.State) (i : N.Inputs) :
  R.v3527 (state s) (inputs i) = Zmod.unsigned (N.v3527 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3527 s i)) at 1.
  unfold R.v3527, N.v3527.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3528 (s : N.State) (i : N.Inputs) :
  R.v3528 (state s) (inputs i) = Zmod.unsigned (N.v3528 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3528 s i)) at 1.
  unfold R.v3528, N.v3528.
  rewrite ?node_3527.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1504_nr_5F1508.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1504_nr_5F1508 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3529 (s : N.State) (i : N.Inputs) :
  R.v3529 (state s) (inputs i) = Zmod.unsigned (N.v3529 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3529 s i)) at 1.
  unfold R.v3529, N.v3529.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3530 (s : N.State) (i : N.Inputs) :
  R.v3530 (state s) (inputs i) = Zmod.unsigned (N.v3530 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3530 s i)) at 1.
  unfold R.v3530, N.v3530.
  rewrite ?node_3529.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1505_nr_5F1509.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1505_nr_5F1509 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3531 (s : N.State) (i : N.Inputs) :
  R.v3531 (state s) (inputs i) = Zmod.unsigned (N.v3531 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3531 s i)) at 1.
  unfold R.v3531, N.v3531.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3532 (s : N.State) (i : N.Inputs) :
  R.v3532 (state s) (inputs i) = Zmod.unsigned (N.v3532 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3532 s i)) at 1.
  unfold R.v3532, N.v3532.
  rewrite ?node_3531.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1506_nr_5F1510.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1506_nr_5F1510 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3533 (s : N.State) (i : N.Inputs) :
  R.v3533 (state s) (inputs i) = Zmod.unsigned (N.v3533 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3533 s i)) at 1.
  unfold R.v3533, N.v3533.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3534 (s : N.State) (i : N.Inputs) :
  R.v3534 (state s) (inputs i) = Zmod.unsigned (N.v3534 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3534 s i)) at 1.
  unfold R.v3534, N.v3534.
  rewrite ?node_3533.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1507_nr_5F1511.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1507_nr_5F1511 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3535 (s : N.State) (i : N.Inputs) :
  R.v3535 (state s) (inputs i) = Zmod.unsigned (N.v3535 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3535 s i)) at 1.
  unfold R.v3535, N.v3535.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3536 (s : N.State) (i : N.Inputs) :
  R.v3536 (state s) (inputs i) = Zmod.unsigned (N.v3536 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3536 s i)) at 1.
  unfold R.v3536, N.v3536.
  rewrite ?node_3535.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1508_nr_5F1512.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1508_nr_5F1512 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3537 (s : N.State) (i : N.Inputs) :
  R.v3537 (state s) (inputs i) = Zmod.unsigned (N.v3537 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3537 s i)) at 1.
  unfold R.v3537, N.v3537.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3538 (s : N.State) (i : N.Inputs) :
  R.v3538 (state s) (inputs i) = Zmod.unsigned (N.v3538 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3538 s i)) at 1.
  unfold R.v3538, N.v3538.
  rewrite ?node_3537.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1509_nr_5F1513.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1509_nr_5F1513 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3539 (s : N.State) (i : N.Inputs) :
  R.v3539 (state s) (inputs i) = Zmod.unsigned (N.v3539 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3539 s i)) at 1.
  unfold R.v3539, N.v3539.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3540 (s : N.State) (i : N.Inputs) :
  R.v3540 (state s) (inputs i) = Zmod.unsigned (N.v3540 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3540 s i)) at 1.
  unfold R.v3540, N.v3540.
  rewrite ?node_3539.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1510_nr_5F1514.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1510_nr_5F1514 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3541 (s : N.State) (i : N.Inputs) :
  R.v3541 (state s) (inputs i) = Zmod.unsigned (N.v3541 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3541 s i)) at 1.
  unfold R.v3541, N.v3541.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3542 (s : N.State) (i : N.Inputs) :
  R.v3542 (state s) (inputs i) = Zmod.unsigned (N.v3542 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3542 s i)) at 1.
  unfold R.v3542, N.v3542.
  rewrite ?node_3541.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1511_nr_5F1515.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1511_nr_5F1515 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3543 (s : N.State) (i : N.Inputs) :
  R.v3543 (state s) (inputs i) = Zmod.unsigned (N.v3543 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3543 s i)) at 1.
  unfold R.v3543, N.v3543.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3544 (s : N.State) (i : N.Inputs) :
  R.v3544 (state s) (inputs i) = Zmod.unsigned (N.v3544 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3544 s i)) at 1.
  unfold R.v3544, N.v3544.
  rewrite ?node_3543.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1512_nr_5F1516.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1512_nr_5F1516 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3545 (s : N.State) (i : N.Inputs) :
  R.v3545 (state s) (inputs i) = Zmod.unsigned (N.v3545 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3545 s i)) at 1.
  unfold R.v3545, N.v3545.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3546 (s : N.State) (i : N.Inputs) :
  R.v3546 (state s) (inputs i) = Zmod.unsigned (N.v3546 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3546 s i)) at 1.
  unfold R.v3546, N.v3546.
  rewrite ?node_3545.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1513_nr_5F1517.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1513_nr_5F1517 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3547 (s : N.State) (i : N.Inputs) :
  R.v3547 (state s) (inputs i) = Zmod.unsigned (N.v3547 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3547 s i)) at 1.
  unfold R.v3547, N.v3547.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3548 (s : N.State) (i : N.Inputs) :
  R.v3548 (state s) (inputs i) = Zmod.unsigned (N.v3548 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3548 s i)) at 1.
  unfold R.v3548, N.v3548.
  rewrite ?node_3547.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1514_nr_5F1518.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1514_nr_5F1518 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3549 (s : N.State) (i : N.Inputs) :
  R.v3549 (state s) (inputs i) = Zmod.unsigned (N.v3549 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3549 s i)) at 1.
  unfold R.v3549, N.v3549.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3550 (s : N.State) (i : N.Inputs) :
  R.v3550 (state s) (inputs i) = Zmod.unsigned (N.v3550 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3550 s i)) at 1.
  unfold R.v3550, N.v3550.
  rewrite ?node_3549.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1515_nr_5F1519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1515_nr_5F1519 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3551 (s : N.State) (i : N.Inputs) :
  R.v3551 (state s) (inputs i) = Zmod.unsigned (N.v3551 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3551 s i)) at 1.
  unfold R.v3551, N.v3551.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3552 (s : N.State) (i : N.Inputs) :
  R.v3552 (state s) (inputs i) = Zmod.unsigned (N.v3552 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3552 s i)) at 1.
  unfold R.v3552, N.v3552.
  rewrite ?node_3551.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1516_nr_5F1520.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1516_nr_5F1520 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3553 (s : N.State) (i : N.Inputs) :
  R.v3553 (state s) (inputs i) = Zmod.unsigned (N.v3553 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3553 s i)) at 1.
  unfold R.v3553, N.v3553.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3554 (s : N.State) (i : N.Inputs) :
  R.v3554 (state s) (inputs i) = Zmod.unsigned (N.v3554 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3554 s i)) at 1.
  unfold R.v3554, N.v3554.
  rewrite ?node_3553.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1517_nr_5F1521.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1517_nr_5F1521 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3555 (s : N.State) (i : N.Inputs) :
  R.v3555 (state s) (inputs i) = Zmod.unsigned (N.v3555 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3555 s i)) at 1.
  unfold R.v3555, N.v3555.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3556 (s : N.State) (i : N.Inputs) :
  R.v3556 (state s) (inputs i) = Zmod.unsigned (N.v3556 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3556 s i)) at 1.
  unfold R.v3556, N.v3556.
  rewrite ?node_3555.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1518_nr_5F1522.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1518_nr_5F1522 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3557 (s : N.State) (i : N.Inputs) :
  R.v3557 (state s) (inputs i) = Zmod.unsigned (N.v3557 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3557 s i)) at 1.
  unfold R.v3557, N.v3557.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3558 (s : N.State) (i : N.Inputs) :
  R.v3558 (state s) (inputs i) = Zmod.unsigned (N.v3558 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3558 s i)) at 1.
  unfold R.v3558, N.v3558.
  rewrite ?node_3557.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1519_nr_5F1523.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1519_nr_5F1523 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3559 (s : N.State) (i : N.Inputs) :
  R.v3559 (state s) (inputs i) = Zmod.unsigned (N.v3559 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3559 s i)) at 1.
  unfold R.v3559, N.v3559.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3560 (s : N.State) (i : N.Inputs) :
  R.v3560 (state s) (inputs i) = Zmod.unsigned (N.v3560 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3560 s i)) at 1.
  unfold R.v3560, N.v3560.
  rewrite ?node_3559.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1520_nr_5F1524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1520_nr_5F1524 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3561 (s : N.State) (i : N.Inputs) :
  R.v3561 (state s) (inputs i) = Zmod.unsigned (N.v3561 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3561 s i)) at 1.
  unfold R.v3561, N.v3561.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3562 (s : N.State) (i : N.Inputs) :
  R.v3562 (state s) (inputs i) = Zmod.unsigned (N.v3562 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3562 s i)) at 1.
  unfold R.v3562, N.v3562.
  rewrite ?node_3561.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1521_nr_5F1525.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1521_nr_5F1525 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3563 (s : N.State) (i : N.Inputs) :
  R.v3563 (state s) (inputs i) = Zmod.unsigned (N.v3563 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3563 s i)) at 1.
  unfold R.v3563, N.v3563.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3564 (s : N.State) (i : N.Inputs) :
  R.v3564 (state s) (inputs i) = Zmod.unsigned (N.v3564 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3564 s i)) at 1.
  unfold R.v3564, N.v3564.
  rewrite ?node_3563.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1522_nr_5F1526.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1522_nr_5F1526 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3565 (s : N.State) (i : N.Inputs) :
  R.v3565 (state s) (inputs i) = Zmod.unsigned (N.v3565 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3565 s i)) at 1.
  unfold R.v3565, N.v3565.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3566 (s : N.State) (i : N.Inputs) :
  R.v3566 (state s) (inputs i) = Zmod.unsigned (N.v3566 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3566 s i)) at 1.
  unfold R.v3566, N.v3566.
  rewrite ?node_3565.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1523_nr_5F1528.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1523_nr_5F1528 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3567 (s : N.State) (i : N.Inputs) :
  R.v3567 (state s) (inputs i) = Zmod.unsigned (N.v3567 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3567 s i)) at 1.
  unfold R.v3567, N.v3567.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3568 (s : N.State) (i : N.Inputs) :
  R.v3568 (state s) (inputs i) = Zmod.unsigned (N.v3568 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3568 s i)) at 1.
  unfold R.v3568, N.v3568.
  rewrite ?node_3567.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1524_nr_5F1529.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1524_nr_5F1529 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3569 (s : N.State) (i : N.Inputs) :
  R.v3569 (state s) (inputs i) = Zmod.unsigned (N.v3569 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3569 s i)) at 1.
  unfold R.v3569, N.v3569.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3570 (s : N.State) (i : N.Inputs) :
  R.v3570 (state s) (inputs i) = Zmod.unsigned (N.v3570 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3570 s i)) at 1.
  unfold R.v3570, N.v3570.
  rewrite ?node_3569.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1525_nr_5F1530.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1525_nr_5F1530 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3571 (s : N.State) (i : N.Inputs) :
  R.v3571 (state s) (inputs i) = Zmod.unsigned (N.v3571 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3571 s i)) at 1.
  unfold R.v3571, N.v3571.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3572 (s : N.State) (i : N.Inputs) :
  R.v3572 (state s) (inputs i) = Zmod.unsigned (N.v3572 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3572 s i)) at 1.
  unfold R.v3572, N.v3572.
  rewrite ?node_3571.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1526_nr_5F1531.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1526_nr_5F1531 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3573 (s : N.State) (i : N.Inputs) :
  R.v3573 (state s) (inputs i) = Zmod.unsigned (N.v3573 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3573 s i)) at 1.
  unfold R.v3573, N.v3573.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3574 (s : N.State) (i : N.Inputs) :
  R.v3574 (state s) (inputs i) = Zmod.unsigned (N.v3574 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3574 s i)) at 1.
  unfold R.v3574, N.v3574.
  rewrite ?node_3573.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1527_nr_5F1532.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1527_nr_5F1532 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3575 (s : N.State) (i : N.Inputs) :
  R.v3575 (state s) (inputs i) = Zmod.unsigned (N.v3575 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3575 s i)) at 1.
  unfold R.v3575, N.v3575.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3576 (s : N.State) (i : N.Inputs) :
  R.v3576 (state s) (inputs i) = Zmod.unsigned (N.v3576 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3576 s i)) at 1.
  unfold R.v3576, N.v3576.
  rewrite ?node_3575.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1528_nr_5F1533.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1528_nr_5F1533 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3577 (s : N.State) (i : N.Inputs) :
  R.v3577 (state s) (inputs i) = Zmod.unsigned (N.v3577 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3577 s i)) at 1.
  unfold R.v3577, N.v3577.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3578 (s : N.State) (i : N.Inputs) :
  R.v3578 (state s) (inputs i) = Zmod.unsigned (N.v3578 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3578 s i)) at 1.
  unfold R.v3578, N.v3578.
  rewrite ?node_3577.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1529_nr_5F1534.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1529_nr_5F1534 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3579 (s : N.State) (i : N.Inputs) :
  R.v3579 (state s) (inputs i) = Zmod.unsigned (N.v3579 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3579 s i)) at 1.
  unfold R.v3579, N.v3579.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3580 (s : N.State) (i : N.Inputs) :
  R.v3580 (state s) (inputs i) = Zmod.unsigned (N.v3580 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3580 s i)) at 1.
  unfold R.v3580, N.v3580.
  rewrite ?node_3579.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1530_nr_5F1535.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1530_nr_5F1535 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3581 (s : N.State) (i : N.Inputs) :
  R.v3581 (state s) (inputs i) = Zmod.unsigned (N.v3581 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3581 s i)) at 1.
  unfold R.v3581, N.v3581.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3582 (s : N.State) (i : N.Inputs) :
  R.v3582 (state s) (inputs i) = Zmod.unsigned (N.v3582 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3582 s i)) at 1.
  unfold R.v3582, N.v3582.
  rewrite ?node_3581.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1531_nr_5F1536.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1531_nr_5F1536 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3583 (s : N.State) (i : N.Inputs) :
  R.v3583 (state s) (inputs i) = Zmod.unsigned (N.v3583 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3583 s i)) at 1.
  unfold R.v3583, N.v3583.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3584 (s : N.State) (i : N.Inputs) :
  R.v3584 (state s) (inputs i) = Zmod.unsigned (N.v3584 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3584 s i)) at 1.
  unfold R.v3584, N.v3584.
  rewrite ?node_3583.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1532_nr_5F1537.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1532_nr_5F1537 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3585 (s : N.State) (i : N.Inputs) :
  R.v3585 (state s) (inputs i) = Zmod.unsigned (N.v3585 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3585 s i)) at 1.
  unfold R.v3585, N.v3585.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3586 (s : N.State) (i : N.Inputs) :
  R.v3586 (state s) (inputs i) = Zmod.unsigned (N.v3586 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3586 s i)) at 1.
  unfold R.v3586, N.v3586.
  rewrite ?node_3585.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1533_nr_5F1538.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1533_nr_5F1538 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3587 (s : N.State) (i : N.Inputs) :
  R.v3587 (state s) (inputs i) = Zmod.unsigned (N.v3587 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3587 s i)) at 1.
  unfold R.v3587, N.v3587.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3588 (s : N.State) (i : N.Inputs) :
  R.v3588 (state s) (inputs i) = Zmod.unsigned (N.v3588 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3588 s i)) at 1.
  unfold R.v3588, N.v3588.
  rewrite ?node_3587.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1534_nr_5F1539.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1534_nr_5F1539 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3589 (s : N.State) (i : N.Inputs) :
  R.v3589 (state s) (inputs i) = Zmod.unsigned (N.v3589 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3589 s i)) at 1.
  unfold R.v3589, N.v3589.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3590 (s : N.State) (i : N.Inputs) :
  R.v3590 (state s) (inputs i) = Zmod.unsigned (N.v3590 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3590 s i)) at 1.
  unfold R.v3590, N.v3590.
  rewrite ?node_3589.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1535_nr_5F1540.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1535_nr_5F1540 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3591 (s : N.State) (i : N.Inputs) :
  R.v3591 (state s) (inputs i) = Zmod.unsigned (N.v3591 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3591 s i)) at 1.
  unfold R.v3591, N.v3591.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3592 (s : N.State) (i : N.Inputs) :
  R.v3592 (state s) (inputs i) = Zmod.unsigned (N.v3592 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3592 s i)) at 1.
  unfold R.v3592, N.v3592.
  rewrite ?node_3591.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1536_nr_5F1541.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1536_nr_5F1541 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3593 (s : N.State) (i : N.Inputs) :
  R.v3593 (state s) (inputs i) = Zmod.unsigned (N.v3593 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3593 s i)) at 1.
  unfold R.v3593, N.v3593.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3594 (s : N.State) (i : N.Inputs) :
  R.v3594 (state s) (inputs i) = Zmod.unsigned (N.v3594 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3594 s i)) at 1.
  unfold R.v3594, N.v3594.
  rewrite ?node_3593.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1537_nr_5F1542.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1537_nr_5F1542 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3595 (s : N.State) (i : N.Inputs) :
  R.v3595 (state s) (inputs i) = Zmod.unsigned (N.v3595 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3595 s i)) at 1.
  unfold R.v3595, N.v3595.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3596 (s : N.State) (i : N.Inputs) :
  R.v3596 (state s) (inputs i) = Zmod.unsigned (N.v3596 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3596 s i)) at 1.
  unfold R.v3596, N.v3596.
  rewrite ?node_3595.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1538_nr_5F1543.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1538_nr_5F1543 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3597 (s : N.State) (i : N.Inputs) :
  R.v3597 (state s) (inputs i) = Zmod.unsigned (N.v3597 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3597 s i)) at 1.
  unfold R.v3597, N.v3597.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3598 (s : N.State) (i : N.Inputs) :
  R.v3598 (state s) (inputs i) = Zmod.unsigned (N.v3598 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3598 s i)) at 1.
  unfold R.v3598, N.v3598.
  rewrite ?node_3597.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1539_nr_5F1544.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1539_nr_5F1544 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3599 (s : N.State) (i : N.Inputs) :
  R.v3599 (state s) (inputs i) = Zmod.unsigned (N.v3599 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3599 s i)) at 1.
  unfold R.v3599, N.v3599.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3600 (s : N.State) (i : N.Inputs) :
  R.v3600 (state s) (inputs i) = Zmod.unsigned (N.v3600 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3600 s i)) at 1.
  unfold R.v3600, N.v3600.
  rewrite ?node_3599.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1540_nr_5F1545.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1540_nr_5F1545 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3601 (s : N.State) (i : N.Inputs) :
  R.v3601 (state s) (inputs i) = Zmod.unsigned (N.v3601 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3601 s i)) at 1.
  unfold R.v3601, N.v3601.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3602 (s : N.State) (i : N.Inputs) :
  R.v3602 (state s) (inputs i) = Zmod.unsigned (N.v3602 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3602 s i)) at 1.
  unfold R.v3602, N.v3602.
  rewrite ?node_3601.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1541_nr_5F1546.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1541_nr_5F1546 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3603 (s : N.State) (i : N.Inputs) :
  R.v3603 (state s) (inputs i) = Zmod.unsigned (N.v3603 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3603 s i)) at 1.
  unfold R.v3603, N.v3603.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3604 (s : N.State) (i : N.Inputs) :
  R.v3604 (state s) (inputs i) = Zmod.unsigned (N.v3604 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3604 s i)) at 1.
  unfold R.v3604, N.v3604.
  rewrite ?node_3603.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1542_nr_5F1547.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1542_nr_5F1547 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3605 (s : N.State) (i : N.Inputs) :
  R.v3605 (state s) (inputs i) = Zmod.unsigned (N.v3605 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3605 s i)) at 1.
  unfold R.v3605, N.v3605.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3606 (s : N.State) (i : N.Inputs) :
  R.v3606 (state s) (inputs i) = Zmod.unsigned (N.v3606 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3606 s i)) at 1.
  unfold R.v3606, N.v3606.
  rewrite ?node_3605.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1543_nr_5F1548.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1543_nr_5F1548 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3607 (s : N.State) (i : N.Inputs) :
  R.v3607 (state s) (inputs i) = Zmod.unsigned (N.v3607 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3607 s i)) at 1.
  unfold R.v3607, N.v3607.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3608 (s : N.State) (i : N.Inputs) :
  R.v3608 (state s) (inputs i) = Zmod.unsigned (N.v3608 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3608 s i)) at 1.
  unfold R.v3608, N.v3608.
  rewrite ?node_3607.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1544_nr_5F1549.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1544_nr_5F1549 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3609 (s : N.State) (i : N.Inputs) :
  R.v3609 (state s) (inputs i) = Zmod.unsigned (N.v3609 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3609 s i)) at 1.
  unfold R.v3609, N.v3609.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3610 (s : N.State) (i : N.Inputs) :
  R.v3610 (state s) (inputs i) = Zmod.unsigned (N.v3610 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3610 s i)) at 1.
  unfold R.v3610, N.v3610.
  rewrite ?node_3609.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1545_nr_5F1550.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1545_nr_5F1550 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3611 (s : N.State) (i : N.Inputs) :
  R.v3611 (state s) (inputs i) = Zmod.unsigned (N.v3611 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3611 s i)) at 1.
  unfold R.v3611, N.v3611.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3612 (s : N.State) (i : N.Inputs) :
  R.v3612 (state s) (inputs i) = Zmod.unsigned (N.v3612 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3612 s i)) at 1.
  unfold R.v3612, N.v3612.
  rewrite ?node_3611.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1546_nr_5F1551.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1546_nr_5F1551 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3613 (s : N.State) (i : N.Inputs) :
  R.v3613 (state s) (inputs i) = Zmod.unsigned (N.v3613 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3613 s i)) at 1.
  unfold R.v3613, N.v3613.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3614 (s : N.State) (i : N.Inputs) :
  R.v3614 (state s) (inputs i) = Zmod.unsigned (N.v3614 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3614 s i)) at 1.
  unfold R.v3614, N.v3614.
  rewrite ?node_3613.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1547_nr_5F1552.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1547_nr_5F1552 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3615 (s : N.State) (i : N.Inputs) :
  R.v3615 (state s) (inputs i) = Zmod.unsigned (N.v3615 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3615 s i)) at 1.
  unfold R.v3615, N.v3615.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3616 (s : N.State) (i : N.Inputs) :
  R.v3616 (state s) (inputs i) = Zmod.unsigned (N.v3616 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3616 s i)) at 1.
  unfold R.v3616, N.v3616.
  rewrite ?node_3615.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1548_nr_5F1553.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1548_nr_5F1553 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3617 (s : N.State) (i : N.Inputs) :
  R.v3617 (state s) (inputs i) = Zmod.unsigned (N.v3617 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3617 s i)) at 1.
  unfold R.v3617, N.v3617.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3618 (s : N.State) (i : N.Inputs) :
  R.v3618 (state s) (inputs i) = Zmod.unsigned (N.v3618 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3618 s i)) at 1.
  unfold R.v3618, N.v3618.
  rewrite ?node_3617.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1549_nr_5F1554.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1549_nr_5F1554 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3619 (s : N.State) (i : N.Inputs) :
  R.v3619 (state s) (inputs i) = Zmod.unsigned (N.v3619 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3619 s i)) at 1.
  unfold R.v3619, N.v3619.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3620 (s : N.State) (i : N.Inputs) :
  R.v3620 (state s) (inputs i) = Zmod.unsigned (N.v3620 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3620 s i)) at 1.
  unfold R.v3620, N.v3620.
  unfold R.v3021, N.v3021.
  rewrite ?node_3619.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3621 (s : N.State) (i : N.Inputs) :
  R.v3621 (state s) (inputs i) = Zmod.unsigned (N.v3621 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3621 s i)) at 1.
  unfold R.v3621, N.v3621.
  rewrite ?node_3620.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1550_nr_5F1555.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1550_nr_5F1555 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3622 (s : N.State) (i : N.Inputs) :
  R.v3622 (state s) (inputs i) = Zmod.unsigned (N.v3622 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3622 s i)) at 1.
  unfold R.v3622, N.v3622.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3623 (s : N.State) (i : N.Inputs) :
  R.v3623 (state s) (inputs i) = Zmod.unsigned (N.v3623 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3623 s i)) at 1.
  unfold R.v3623, N.v3623.
  rewrite ?node_3622.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1551_nr_5F1556.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1551_nr_5F1556 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3624 (s : N.State) (i : N.Inputs) :
  R.v3624 (state s) (inputs i) = Zmod.unsigned (N.v3624 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3624 s i)) at 1.
  unfold R.v3624, N.v3624.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3625 (s : N.State) (i : N.Inputs) :
  R.v3625 (state s) (inputs i) = Zmod.unsigned (N.v3625 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3625 s i)) at 1.
  unfold R.v3625, N.v3625.
  rewrite ?node_3624.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1552_nr_5F1557.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1552_nr_5F1557 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3626 (s : N.State) (i : N.Inputs) :
  R.v3626 (state s) (inputs i) = Zmod.unsigned (N.v3626 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3626 s i)) at 1.
  unfold R.v3626, N.v3626.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3627 (s : N.State) (i : N.Inputs) :
  R.v3627 (state s) (inputs i) = Zmod.unsigned (N.v3627 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3627 s i)) at 1.
  unfold R.v3627, N.v3627.
  rewrite ?node_3626.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1553_nr_5F1558.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1553_nr_5F1558 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3628 (s : N.State) (i : N.Inputs) :
  R.v3628 (state s) (inputs i) = Zmod.unsigned (N.v3628 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3628 s i)) at 1.
  unfold R.v3628, N.v3628.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3629 (s : N.State) (i : N.Inputs) :
  R.v3629 (state s) (inputs i) = Zmod.unsigned (N.v3629 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3629 s i)) at 1.
  unfold R.v3629, N.v3629.
  rewrite ?node_3628.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1554_nr_5F1559.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1554_nr_5F1559 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3630 (s : N.State) (i : N.Inputs) :
  R.v3630 (state s) (inputs i) = Zmod.unsigned (N.v3630 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3630 s i)) at 1.
  unfold R.v3630, N.v3630.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3631 (s : N.State) (i : N.Inputs) :
  R.v3631 (state s) (inputs i) = Zmod.unsigned (N.v3631 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3631 s i)) at 1.
  unfold R.v3631, N.v3631.
  rewrite ?node_3630.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1555_nr_5F1560.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1555_nr_5F1560 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3632 (s : N.State) (i : N.Inputs) :
  R.v3632 (state s) (inputs i) = Zmod.unsigned (N.v3632 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3632 s i)) at 1.
  unfold R.v3632, N.v3632.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3633 (s : N.State) (i : N.Inputs) :
  R.v3633 (state s) (inputs i) = Zmod.unsigned (N.v3633 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3633 s i)) at 1.
  unfold R.v3633, N.v3633.
  rewrite ?node_3632.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1556_nr_5F1561.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1556_nr_5F1561 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3634 (s : N.State) (i : N.Inputs) :
  R.v3634 (state s) (inputs i) = Zmod.unsigned (N.v3634 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3634 s i)) at 1.
  unfold R.v3634, N.v3634.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3635 (s : N.State) (i : N.Inputs) :
  R.v3635 (state s) (inputs i) = Zmod.unsigned (N.v3635 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3635 s i)) at 1.
  unfold R.v3635, N.v3635.
  rewrite ?node_3634.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1557_nr_5F1562.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1557_nr_5F1562 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3636 (s : N.State) (i : N.Inputs) :
  R.v3636 (state s) (inputs i) = Zmod.unsigned (N.v3636 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3636 s i)) at 1.
  unfold R.v3636, N.v3636.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3637 (s : N.State) (i : N.Inputs) :
  R.v3637 (state s) (inputs i) = Zmod.unsigned (N.v3637 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3637 s i)) at 1.
  unfold R.v3637, N.v3637.
  rewrite ?node_3636.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1558_nr_5F1563.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1558_nr_5F1563 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3638 (s : N.State) (i : N.Inputs) :
  R.v3638 (state s) (inputs i) = Zmod.unsigned (N.v3638 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3638 s i)) at 1.
  unfold R.v3638, N.v3638.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3639 (s : N.State) (i : N.Inputs) :
  R.v3639 (state s) (inputs i) = Zmod.unsigned (N.v3639 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3639 s i)) at 1.
  unfold R.v3639, N.v3639.
  rewrite ?node_3638.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1559_nr_5F1564.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1559_nr_5F1564 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3640 (s : N.State) (i : N.Inputs) :
  R.v3640 (state s) (inputs i) = Zmod.unsigned (N.v3640 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3640 s i)) at 1.
  unfold R.v3640, N.v3640.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3641 (s : N.State) (i : N.Inputs) :
  R.v3641 (state s) (inputs i) = Zmod.unsigned (N.v3641 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3641 s i)) at 1.
  unfold R.v3641, N.v3641.
  rewrite ?node_3640.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1560_nr_5F1565.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1560_nr_5F1565 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3642 (s : N.State) (i : N.Inputs) :
  R.v3642 (state s) (inputs i) = Zmod.unsigned (N.v3642 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3642 s i)) at 1.
  unfold R.v3642, N.v3642.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3643 (s : N.State) (i : N.Inputs) :
  R.v3643 (state s) (inputs i) = Zmod.unsigned (N.v3643 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3643 s i)) at 1.
  unfold R.v3643, N.v3643.
  rewrite ?node_3642.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1561_nr_5F1566.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1561_nr_5F1566 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3644 (s : N.State) (i : N.Inputs) :
  R.v3644 (state s) (inputs i) = Zmod.unsigned (N.v3644 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3644 s i)) at 1.
  unfold R.v3644, N.v3644.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3645 (s : N.State) (i : N.Inputs) :
  R.v3645 (state s) (inputs i) = Zmod.unsigned (N.v3645 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3645 s i)) at 1.
  unfold R.v3645, N.v3645.
  rewrite ?node_3644.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1562_nr_5F1567.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1562_nr_5F1567 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3646 (s : N.State) (i : N.Inputs) :
  R.v3646 (state s) (inputs i) = Zmod.unsigned (N.v3646 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3646 s i)) at 1.
  unfold R.v3646, N.v3646.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3647 (s : N.State) (i : N.Inputs) :
  R.v3647 (state s) (inputs i) = Zmod.unsigned (N.v3647 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3647 s i)) at 1.
  unfold R.v3647, N.v3647.
  rewrite ?node_3646.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1563_nr_5F1568.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1563_nr_5F1568 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3648 (s : N.State) (i : N.Inputs) :
  R.v3648 (state s) (inputs i) = Zmod.unsigned (N.v3648 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3648 s i)) at 1.
  unfold R.v3648, N.v3648.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3649 (s : N.State) (i : N.Inputs) :
  R.v3649 (state s) (inputs i) = Zmod.unsigned (N.v3649 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3649 s i)) at 1.
  unfold R.v3649, N.v3649.
  rewrite ?node_3648.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1564_nr_5F1569.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1564_nr_5F1569 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3650 (s : N.State) (i : N.Inputs) :
  R.v3650 (state s) (inputs i) = Zmod.unsigned (N.v3650 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3650 s i)) at 1.
  unfold R.v3650, N.v3650.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3651 (s : N.State) (i : N.Inputs) :
  R.v3651 (state s) (inputs i) = Zmod.unsigned (N.v3651 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3651 s i)) at 1.
  unfold R.v3651, N.v3651.
  rewrite ?node_3650.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1565_nr_5F1570.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1565_nr_5F1570 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3652 (s : N.State) (i : N.Inputs) :
  R.v3652 (state s) (inputs i) = Zmod.unsigned (N.v3652 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3652 s i)) at 1.
  unfold R.v3652, N.v3652.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3653 (s : N.State) (i : N.Inputs) :
  R.v3653 (state s) (inputs i) = Zmod.unsigned (N.v3653 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3653 s i)) at 1.
  unfold R.v3653, N.v3653.
  rewrite ?node_3652.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1566_nr_5F1571.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1566_nr_5F1571 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3654 (s : N.State) (i : N.Inputs) :
  R.v3654 (state s) (inputs i) = Zmod.unsigned (N.v3654 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3654 s i)) at 1.
  unfold R.v3654, N.v3654.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3655 (s : N.State) (i : N.Inputs) :
  R.v3655 (state s) (inputs i) = Zmod.unsigned (N.v3655 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3655 s i)) at 1.
  unfold R.v3655, N.v3655.
  rewrite ?node_3654.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1567_nr_5F1572.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1567_nr_5F1572 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3656 (s : N.State) (i : N.Inputs) :
  R.v3656 (state s) (inputs i) = Zmod.unsigned (N.v3656 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3656 s i)) at 1.
  unfold R.v3656, N.v3656.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3657 (s : N.State) (i : N.Inputs) :
  R.v3657 (state s) (inputs i) = Zmod.unsigned (N.v3657 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3657 s i)) at 1.
  unfold R.v3657, N.v3657.
  rewrite ?node_3656.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1568_nr_5F1573.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1568_nr_5F1573 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3658 (s : N.State) (i : N.Inputs) :
  R.v3658 (state s) (inputs i) = Zmod.unsigned (N.v3658 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3658 s i)) at 1.
  unfold R.v3658, N.v3658.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3659 (s : N.State) (i : N.Inputs) :
  R.v3659 (state s) (inputs i) = Zmod.unsigned (N.v3659 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3659 s i)) at 1.
  unfold R.v3659, N.v3659.
  rewrite ?node_3658.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1569_nr_5F1574.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1569_nr_5F1574 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3660 (s : N.State) (i : N.Inputs) :
  R.v3660 (state s) (inputs i) = Zmod.unsigned (N.v3660 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3660 s i)) at 1.
  unfold R.v3660, N.v3660.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3661 (s : N.State) (i : N.Inputs) :
  R.v3661 (state s) (inputs i) = Zmod.unsigned (N.v3661 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3661 s i)) at 1.
  unfold R.v3661, N.v3661.
  rewrite ?node_3660.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1570_nr_5F1575.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1570_nr_5F1575 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3662 (s : N.State) (i : N.Inputs) :
  R.v3662 (state s) (inputs i) = Zmod.unsigned (N.v3662 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3662 s i)) at 1.
  unfold R.v3662, N.v3662.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3663 (s : N.State) (i : N.Inputs) :
  R.v3663 (state s) (inputs i) = Zmod.unsigned (N.v3663 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3663 s i)) at 1.
  unfold R.v3663, N.v3663.
  rewrite ?node_3662.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1571_nr_5F1576.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1571_nr_5F1576 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3664 (s : N.State) (i : N.Inputs) :
  R.v3664 (state s) (inputs i) = Zmod.unsigned (N.v3664 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3664 s i)) at 1.
  unfold R.v3664, N.v3664.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3665 (s : N.State) (i : N.Inputs) :
  R.v3665 (state s) (inputs i) = Zmod.unsigned (N.v3665 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3665 s i)) at 1.
  unfold R.v3665, N.v3665.
  rewrite ?node_3664.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1572_nr_5F1577.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1572_nr_5F1577 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3666 (s : N.State) (i : N.Inputs) :
  R.v3666 (state s) (inputs i) = Zmod.unsigned (N.v3666 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3666 s i)) at 1.
  unfold R.v3666, N.v3666.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3667 (s : N.State) (i : N.Inputs) :
  R.v3667 (state s) (inputs i) = Zmod.unsigned (N.v3667 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3667 s i)) at 1.
  unfold R.v3667, N.v3667.
  rewrite ?node_3666.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1573_nr_5F1578.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1573_nr_5F1578 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3668 (s : N.State) (i : N.Inputs) :
  R.v3668 (state s) (inputs i) = Zmod.unsigned (N.v3668 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3668 s i)) at 1.
  unfold R.v3668, N.v3668.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3669 (s : N.State) (i : N.Inputs) :
  R.v3669 (state s) (inputs i) = Zmod.unsigned (N.v3669 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3669 s i)) at 1.
  unfold R.v3669, N.v3669.
  rewrite ?node_3668.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1574_nr_5F1579.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1574_nr_5F1579 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3670 (s : N.State) (i : N.Inputs) :
  R.v3670 (state s) (inputs i) = Zmod.unsigned (N.v3670 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3670 s i)) at 1.
  unfold R.v3670, N.v3670.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3671 (s : N.State) (i : N.Inputs) :
  R.v3671 (state s) (inputs i) = Zmod.unsigned (N.v3671 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3671 s i)) at 1.
  unfold R.v3671, N.v3671.
  rewrite ?node_3670.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1575_nr_5F1580.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1575_nr_5F1580 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3672 (s : N.State) (i : N.Inputs) :
  R.v3672 (state s) (inputs i) = Zmod.unsigned (N.v3672 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3672 s i)) at 1.
  unfold R.v3672, N.v3672.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3673 (s : N.State) (i : N.Inputs) :
  R.v3673 (state s) (inputs i) = Zmod.unsigned (N.v3673 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3673 s i)) at 1.
  unfold R.v3673, N.v3673.
  rewrite ?node_3672.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1576_nr_5F1581.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1576_nr_5F1581 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3674 (s : N.State) (i : N.Inputs) :
  R.v3674 (state s) (inputs i) = Zmod.unsigned (N.v3674 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3674 s i)) at 1.
  unfold R.v3674, N.v3674.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3675 (s : N.State) (i : N.Inputs) :
  R.v3675 (state s) (inputs i) = Zmod.unsigned (N.v3675 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3675 s i)) at 1.
  unfold R.v3675, N.v3675.
  rewrite ?node_3674.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1577_nr_5F1583.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1577_nr_5F1583 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3676 (s : N.State) (i : N.Inputs) :
  R.v3676 (state s) (inputs i) = Zmod.unsigned (N.v3676 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3676 s i)) at 1.
  unfold R.v3676, N.v3676.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3677 (s : N.State) (i : N.Inputs) :
  R.v3677 (state s) (inputs i) = Zmod.unsigned (N.v3677 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3677 s i)) at 1.
  unfold R.v3677, N.v3677.
  rewrite ?node_3676.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1578_nr_5F1584.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1578_nr_5F1584 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3678 (s : N.State) (i : N.Inputs) :
  R.v3678 (state s) (inputs i) = Zmod.unsigned (N.v3678 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3678 s i)) at 1.
  unfold R.v3678, N.v3678.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3679 (s : N.State) (i : N.Inputs) :
  R.v3679 (state s) (inputs i) = Zmod.unsigned (N.v3679 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3679 s i)) at 1.
  unfold R.v3679, N.v3679.
  rewrite ?node_3678.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1579_nr_5F1585.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1579_nr_5F1585 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3680 (s : N.State) (i : N.Inputs) :
  R.v3680 (state s) (inputs i) = Zmod.unsigned (N.v3680 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3680 s i)) at 1.
  unfold R.v3680, N.v3680.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3681 (s : N.State) (i : N.Inputs) :
  R.v3681 (state s) (inputs i) = Zmod.unsigned (N.v3681 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3681 s i)) at 1.
  unfold R.v3681, N.v3681.
  rewrite ?node_3680.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1580_nr_5F1586.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1580_nr_5F1586 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3682 (s : N.State) (i : N.Inputs) :
  R.v3682 (state s) (inputs i) = Zmod.unsigned (N.v3682 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3682 s i)) at 1.
  unfold R.v3682, N.v3682.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3683 (s : N.State) (i : N.Inputs) :
  R.v3683 (state s) (inputs i) = Zmod.unsigned (N.v3683 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3683 s i)) at 1.
  unfold R.v3683, N.v3683.
  rewrite ?node_3682.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1581_nr_5F1587.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1581_nr_5F1587 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3684 (s : N.State) (i : N.Inputs) :
  R.v3684 (state s) (inputs i) = Zmod.unsigned (N.v3684 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3684 s i)) at 1.
  unfold R.v3684, N.v3684.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3685 (s : N.State) (i : N.Inputs) :
  R.v3685 (state s) (inputs i) = Zmod.unsigned (N.v3685 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3685 s i)) at 1.
  unfold R.v3685, N.v3685.
  rewrite ?node_3684.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1582_nr_5F1588.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1582_nr_5F1588 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3686 (s : N.State) (i : N.Inputs) :
  R.v3686 (state s) (inputs i) = Zmod.unsigned (N.v3686 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3686 s i)) at 1.
  unfold R.v3686, N.v3686.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3687 (s : N.State) (i : N.Inputs) :
  R.v3687 (state s) (inputs i) = Zmod.unsigned (N.v3687 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3687 s i)) at 1.
  unfold R.v3687, N.v3687.
  rewrite ?node_3686.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1583_nr_5F1589.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1583_nr_5F1589 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3688 (s : N.State) (i : N.Inputs) :
  R.v3688 (state s) (inputs i) = Zmod.unsigned (N.v3688 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3688 s i)) at 1.
  unfold R.v3688, N.v3688.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3689 (s : N.State) (i : N.Inputs) :
  R.v3689 (state s) (inputs i) = Zmod.unsigned (N.v3689 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3689 s i)) at 1.
  unfold R.v3689, N.v3689.
  rewrite ?node_3688.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1584_nr_5F1590.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1584_nr_5F1590 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3690 (s : N.State) (i : N.Inputs) :
  R.v3690 (state s) (inputs i) = Zmod.unsigned (N.v3690 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3690 s i)) at 1.
  unfold R.v3690, N.v3690.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3691 (s : N.State) (i : N.Inputs) :
  R.v3691 (state s) (inputs i) = Zmod.unsigned (N.v3691 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3691 s i)) at 1.
  unfold R.v3691, N.v3691.
  rewrite ?node_3690.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1585_nr_5F1591.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1585_nr_5F1591 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3692 (s : N.State) (i : N.Inputs) :
  R.v3692 (state s) (inputs i) = Zmod.unsigned (N.v3692 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3692 s i)) at 1.
  unfold R.v3692, N.v3692.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3693 (s : N.State) (i : N.Inputs) :
  R.v3693 (state s) (inputs i) = Zmod.unsigned (N.v3693 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3693 s i)) at 1.
  unfold R.v3693, N.v3693.
  rewrite ?node_3692.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1586_nr_5F1592.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1586_nr_5F1592 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3694 (s : N.State) (i : N.Inputs) :
  R.v3694 (state s) (inputs i) = Zmod.unsigned (N.v3694 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3694 s i)) at 1.
  unfold R.v3694, N.v3694.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3695 (s : N.State) (i : N.Inputs) :
  R.v3695 (state s) (inputs i) = Zmod.unsigned (N.v3695 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3695 s i)) at 1.
  unfold R.v3695, N.v3695.
  rewrite ?node_3694.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1587_nr_5F1593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1587_nr_5F1593 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3696 (s : N.State) (i : N.Inputs) :
  R.v3696 (state s) (inputs i) = Zmod.unsigned (N.v3696 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3696 s i)) at 1.
  unfold R.v3696, N.v3696.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3697 (s : N.State) (i : N.Inputs) :
  R.v3697 (state s) (inputs i) = Zmod.unsigned (N.v3697 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3697 s i)) at 1.
  unfold R.v3697, N.v3697.
  rewrite ?node_3696.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1588_nr_5F1594.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1588_nr_5F1594 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3698 (s : N.State) (i : N.Inputs) :
  R.v3698 (state s) (inputs i) = Zmod.unsigned (N.v3698 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3698 s i)) at 1.
  unfold R.v3698, N.v3698.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3699 (s : N.State) (i : N.Inputs) :
  R.v3699 (state s) (inputs i) = Zmod.unsigned (N.v3699 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3699 s i)) at 1.
  unfold R.v3699, N.v3699.
  rewrite ?node_3698.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1589_nr_5F1595.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1589_nr_5F1595 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3700 (s : N.State) (i : N.Inputs) :
  R.v3700 (state s) (inputs i) = Zmod.unsigned (N.v3700 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3700 s i)) at 1.
  unfold R.v3700, N.v3700.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3701 (s : N.State) (i : N.Inputs) :
  R.v3701 (state s) (inputs i) = Zmod.unsigned (N.v3701 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3701 s i)) at 1.
  unfold R.v3701, N.v3701.
  rewrite ?node_3700.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1590_nr_5F1596.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1590_nr_5F1596 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3702 (s : N.State) (i : N.Inputs) :
  R.v3702 (state s) (inputs i) = Zmod.unsigned (N.v3702 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3702 s i)) at 1.
  unfold R.v3702, N.v3702.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3703 (s : N.State) (i : N.Inputs) :
  R.v3703 (state s) (inputs i) = Zmod.unsigned (N.v3703 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3703 s i)) at 1.
  unfold R.v3703, N.v3703.
  rewrite ?node_3702.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1591_nr_5F1597.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1591_nr_5F1597 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3704 (s : N.State) (i : N.Inputs) :
  R.v3704 (state s) (inputs i) = Zmod.unsigned (N.v3704 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3704 s i)) at 1.
  unfold R.v3704, N.v3704.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3705 (s : N.State) (i : N.Inputs) :
  R.v3705 (state s) (inputs i) = Zmod.unsigned (N.v3705 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3705 s i)) at 1.
  unfold R.v3705, N.v3705.
  rewrite ?node_3704.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1592_nr_5F1598.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1592_nr_5F1598 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3706 (s : N.State) (i : N.Inputs) :
  R.v3706 (state s) (inputs i) = Zmod.unsigned (N.v3706 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3706 s i)) at 1.
  unfold R.v3706, N.v3706.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3707 (s : N.State) (i : N.Inputs) :
  R.v3707 (state s) (inputs i) = Zmod.unsigned (N.v3707 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3707 s i)) at 1.
  unfold R.v3707, N.v3707.
  rewrite ?node_3706.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1593_nr_5F1599.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1593_nr_5F1599 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3708 (s : N.State) (i : N.Inputs) :
  R.v3708 (state s) (inputs i) = Zmod.unsigned (N.v3708 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3708 s i)) at 1.
  unfold R.v3708, N.v3708.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3709 (s : N.State) (i : N.Inputs) :
  R.v3709 (state s) (inputs i) = Zmod.unsigned (N.v3709 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3709 s i)) at 1.
  unfold R.v3709, N.v3709.
  rewrite ?node_3708.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1594_nr_5F1600.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1594_nr_5F1600 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3710 (s : N.State) (i : N.Inputs) :
  R.v3710 (state s) (inputs i) = Zmod.unsigned (N.v3710 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3710 s i)) at 1.
  unfold R.v3710, N.v3710.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3711 (s : N.State) (i : N.Inputs) :
  R.v3711 (state s) (inputs i) = Zmod.unsigned (N.v3711 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3711 s i)) at 1.
  unfold R.v3711, N.v3711.
  rewrite ?node_3710.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1595_nr_5F1601.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1595_nr_5F1601 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3712 (s : N.State) (i : N.Inputs) :
  R.v3712 (state s) (inputs i) = Zmod.unsigned (N.v3712 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3712 s i)) at 1.
  unfold R.v3712, N.v3712.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3713 (s : N.State) (i : N.Inputs) :
  R.v3713 (state s) (inputs i) = Zmod.unsigned (N.v3713 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3713 s i)) at 1.
  unfold R.v3713, N.v3713.
  rewrite ?node_3712.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1596_nr_5F1602.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1596_nr_5F1602 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3714 (s : N.State) (i : N.Inputs) :
  R.v3714 (state s) (inputs i) = Zmod.unsigned (N.v3714 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3714 s i)) at 1.
  unfold R.v3714, N.v3714.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3715 (s : N.State) (i : N.Inputs) :
  R.v3715 (state s) (inputs i) = Zmod.unsigned (N.v3715 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3715 s i)) at 1.
  unfold R.v3715, N.v3715.
  rewrite ?node_3714.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1597_nr_5F1603.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1597_nr_5F1603 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3716 (s : N.State) (i : N.Inputs) :
  R.v3716 (state s) (inputs i) = Zmod.unsigned (N.v3716 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3716 s i)) at 1.
  unfold R.v3716, N.v3716.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3717 (s : N.State) (i : N.Inputs) :
  R.v3717 (state s) (inputs i) = Zmod.unsigned (N.v3717 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3717 s i)) at 1.
  unfold R.v3717, N.v3717.
  rewrite ?node_3716.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1598_nr_5F1604.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1598_nr_5F1604 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3718 (s : N.State) (i : N.Inputs) :
  R.v3718 (state s) (inputs i) = Zmod.unsigned (N.v3718 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3718 s i)) at 1.
  unfold R.v3718, N.v3718.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3719 (s : N.State) (i : N.Inputs) :
  R.v3719 (state s) (inputs i) = Zmod.unsigned (N.v3719 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3719 s i)) at 1.
  unfold R.v3719, N.v3719.
  rewrite ?node_3718.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1599_nr_5F1605.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1599_nr_5F1605 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3720 (s : N.State) (i : N.Inputs) :
  R.v3720 (state s) (inputs i) = Zmod.unsigned (N.v3720 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3720 s i)) at 1.
  unfold R.v3720, N.v3720.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3721 (s : N.State) (i : N.Inputs) :
  R.v3721 (state s) (inputs i) = Zmod.unsigned (N.v3721 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3721 s i)) at 1.
  unfold R.v3721, N.v3721.
  rewrite ?node_3720.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1600_nr_5F1606.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1600_nr_5F1606 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3722 (s : N.State) (i : N.Inputs) :
  R.v3722 (state s) (inputs i) = Zmod.unsigned (N.v3722 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3722 s i)) at 1.
  unfold R.v3722, N.v3722.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3723 (s : N.State) (i : N.Inputs) :
  R.v3723 (state s) (inputs i) = Zmod.unsigned (N.v3723 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3723 s i)) at 1.
  unfold R.v3723, N.v3723.
  rewrite ?node_3722.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1601_nr_5F1607.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1601_nr_5F1607 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3724 (s : N.State) (i : N.Inputs) :
  R.v3724 (state s) (inputs i) = Zmod.unsigned (N.v3724 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3724 s i)) at 1.
  unfold R.v3724, N.v3724.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3725 (s : N.State) (i : N.Inputs) :
  R.v3725 (state s) (inputs i) = Zmod.unsigned (N.v3725 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3725 s i)) at 1.
  unfold R.v3725, N.v3725.
  rewrite ?node_3724.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1602_nr_5F1608.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1602_nr_5F1608 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3726 (s : N.State) (i : N.Inputs) :
  R.v3726 (state s) (inputs i) = Zmod.unsigned (N.v3726 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3726 s i)) at 1.
  unfold R.v3726, N.v3726.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3727 (s : N.State) (i : N.Inputs) :
  R.v3727 (state s) (inputs i) = Zmod.unsigned (N.v3727 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3727 s i)) at 1.
  unfold R.v3727, N.v3727.
  unfold R.v3021, N.v3021.
  rewrite ?node_3726.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3728 (s : N.State) (i : N.Inputs) :
  R.v3728 (state s) (inputs i) = Zmod.unsigned (N.v3728 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3728 s i)) at 1.
  unfold R.v3728, N.v3728.
  rewrite ?node_3727.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1603_nr_5F1609.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1603_nr_5F1609 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3729 (s : N.State) (i : N.Inputs) :
  R.v3729 (state s) (inputs i) = Zmod.unsigned (N.v3729 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3729 s i)) at 1.
  unfold R.v3729, N.v3729.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3730 (s : N.State) (i : N.Inputs) :
  R.v3730 (state s) (inputs i) = Zmod.unsigned (N.v3730 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3730 s i)) at 1.
  unfold R.v3730, N.v3730.
  rewrite ?node_3729.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1604_nr_5F1610.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1604_nr_5F1610 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3731 (s : N.State) (i : N.Inputs) :
  R.v3731 (state s) (inputs i) = Zmod.unsigned (N.v3731 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3731 s i)) at 1.
  unfold R.v3731, N.v3731.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3732 (s : N.State) (i : N.Inputs) :
  R.v3732 (state s) (inputs i) = Zmod.unsigned (N.v3732 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3732 s i)) at 1.
  unfold R.v3732, N.v3732.
  rewrite ?node_3731.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1605_nr_5F1611.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1605_nr_5F1611 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3733 (s : N.State) (i : N.Inputs) :
  R.v3733 (state s) (inputs i) = Zmod.unsigned (N.v3733 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3733 s i)) at 1.
  unfold R.v3733, N.v3733.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3734 (s : N.State) (i : N.Inputs) :
  R.v3734 (state s) (inputs i) = Zmod.unsigned (N.v3734 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3734 s i)) at 1.
  unfold R.v3734, N.v3734.
  rewrite ?node_3733.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1606_nr_5F1612.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1606_nr_5F1612 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3735 (s : N.State) (i : N.Inputs) :
  R.v3735 (state s) (inputs i) = Zmod.unsigned (N.v3735 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3735 s i)) at 1.
  unfold R.v3735, N.v3735.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3736 (s : N.State) (i : N.Inputs) :
  R.v3736 (state s) (inputs i) = Zmod.unsigned (N.v3736 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3736 s i)) at 1.
  unfold R.v3736, N.v3736.
  rewrite ?node_3735.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1607_nr_5F1613.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1607_nr_5F1613 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3737 (s : N.State) (i : N.Inputs) :
  R.v3737 (state s) (inputs i) = Zmod.unsigned (N.v3737 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3737 s i)) at 1.
  unfold R.v3737, N.v3737.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3738 (s : N.State) (i : N.Inputs) :
  R.v3738 (state s) (inputs i) = Zmod.unsigned (N.v3738 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3738 s i)) at 1.
  unfold R.v3738, N.v3738.
  rewrite ?node_3737.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1608_nr_5F1614.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1608_nr_5F1614 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3739 (s : N.State) (i : N.Inputs) :
  R.v3739 (state s) (inputs i) = Zmod.unsigned (N.v3739 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3739 s i)) at 1.
  unfold R.v3739, N.v3739.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3740 (s : N.State) (i : N.Inputs) :
  R.v3740 (state s) (inputs i) = Zmod.unsigned (N.v3740 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3740 s i)) at 1.
  unfold R.v3740, N.v3740.
  rewrite ?node_3739.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1609_nr_5F1615.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1609_nr_5F1615 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3741 (s : N.State) (i : N.Inputs) :
  R.v3741 (state s) (inputs i) = Zmod.unsigned (N.v3741 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3741 s i)) at 1.
  unfold R.v3741, N.v3741.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3742 (s : N.State) (i : N.Inputs) :
  R.v3742 (state s) (inputs i) = Zmod.unsigned (N.v3742 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3742 s i)) at 1.
  unfold R.v3742, N.v3742.
  rewrite ?node_3741.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1610_nr_5F1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1610_nr_5F1616 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3743 (s : N.State) (i : N.Inputs) :
  R.v3743 (state s) (inputs i) = Zmod.unsigned (N.v3743 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3743 s i)) at 1.
  unfold R.v3743, N.v3743.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3744 (s : N.State) (i : N.Inputs) :
  R.v3744 (state s) (inputs i) = Zmod.unsigned (N.v3744 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3744 s i)) at 1.
  unfold R.v3744, N.v3744.
  rewrite ?node_3743.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1611_nr_5F1617.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1611_nr_5F1617 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3745 (s : N.State) (i : N.Inputs) :
  R.v3745 (state s) (inputs i) = Zmod.unsigned (N.v3745 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3745 s i)) at 1.
  unfold R.v3745, N.v3745.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3746 (s : N.State) (i : N.Inputs) :
  R.v3746 (state s) (inputs i) = Zmod.unsigned (N.v3746 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3746 s i)) at 1.
  unfold R.v3746, N.v3746.
  rewrite ?node_3745.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1612_nr_5F1618.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1612_nr_5F1618 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3747 (s : N.State) (i : N.Inputs) :
  R.v3747 (state s) (inputs i) = Zmod.unsigned (N.v3747 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3747 s i)) at 1.
  unfold R.v3747, N.v3747.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3748 (s : N.State) (i : N.Inputs) :
  R.v3748 (state s) (inputs i) = Zmod.unsigned (N.v3748 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3748 s i)) at 1.
  unfold R.v3748, N.v3748.
  rewrite ?node_3747.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1613_nr_5F1619.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1613_nr_5F1619 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3749 (s : N.State) (i : N.Inputs) :
  R.v3749 (state s) (inputs i) = Zmod.unsigned (N.v3749 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3749 s i)) at 1.
  unfold R.v3749, N.v3749.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3750 (s : N.State) (i : N.Inputs) :
  R.v3750 (state s) (inputs i) = Zmod.unsigned (N.v3750 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3750 s i)) at 1.
  unfold R.v3750, N.v3750.
  rewrite ?node_3749.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1614_nr_5F1620.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1614_nr_5F1620 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3751 (s : N.State) (i : N.Inputs) :
  R.v3751 (state s) (inputs i) = Zmod.unsigned (N.v3751 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3751 s i)) at 1.
  unfold R.v3751, N.v3751.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3752 (s : N.State) (i : N.Inputs) :
  R.v3752 (state s) (inputs i) = Zmod.unsigned (N.v3752 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3752 s i)) at 1.
  unfold R.v3752, N.v3752.
  rewrite ?node_3751.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1615_nr_5F1621.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1615_nr_5F1621 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3753 (s : N.State) (i : N.Inputs) :
  R.v3753 (state s) (inputs i) = Zmod.unsigned (N.v3753 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3753 s i)) at 1.
  unfold R.v3753, N.v3753.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3754 (s : N.State) (i : N.Inputs) :
  R.v3754 (state s) (inputs i) = Zmod.unsigned (N.v3754 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3754 s i)) at 1.
  unfold R.v3754, N.v3754.
  rewrite ?node_3753.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1616_nr_5F1622.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1616_nr_5F1622 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3755 (s : N.State) (i : N.Inputs) :
  R.v3755 (state s) (inputs i) = Zmod.unsigned (N.v3755 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3755 s i)) at 1.
  unfold R.v3755, N.v3755.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3756 (s : N.State) (i : N.Inputs) :
  R.v3756 (state s) (inputs i) = Zmod.unsigned (N.v3756 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3756 s i)) at 1.
  unfold R.v3756, N.v3756.
  rewrite ?node_3755.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1617_nr_5F1623.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1617_nr_5F1623 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3757 (s : N.State) (i : N.Inputs) :
  R.v3757 (state s) (inputs i) = Zmod.unsigned (N.v3757 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3757 s i)) at 1.
  unfold R.v3757, N.v3757.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3758 (s : N.State) (i : N.Inputs) :
  R.v3758 (state s) (inputs i) = Zmod.unsigned (N.v3758 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3758 s i)) at 1.
  unfold R.v3758, N.v3758.
  rewrite ?node_3757.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1618_nr_5F1624.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1618_nr_5F1624 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3759 (s : N.State) (i : N.Inputs) :
  R.v3759 (state s) (inputs i) = Zmod.unsigned (N.v3759 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3759 s i)) at 1.
  unfold R.v3759, N.v3759.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3760 (s : N.State) (i : N.Inputs) :
  R.v3760 (state s) (inputs i) = Zmod.unsigned (N.v3760 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3760 s i)) at 1.
  unfold R.v3760, N.v3760.
  rewrite ?node_3759.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1619_nr_5F1625.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1619_nr_5F1625 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3761 (s : N.State) (i : N.Inputs) :
  R.v3761 (state s) (inputs i) = Zmod.unsigned (N.v3761 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3761 s i)) at 1.
  unfold R.v3761, N.v3761.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3762 (s : N.State) (i : N.Inputs) :
  R.v3762 (state s) (inputs i) = Zmod.unsigned (N.v3762 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3762 s i)) at 1.
  unfold R.v3762, N.v3762.
  rewrite ?node_3761.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1620_nr_5F1626.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1620_nr_5F1626 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3763 (s : N.State) (i : N.Inputs) :
  R.v3763 (state s) (inputs i) = Zmod.unsigned (N.v3763 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3763 s i)) at 1.
  unfold R.v3763, N.v3763.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3764 (s : N.State) (i : N.Inputs) :
  R.v3764 (state s) (inputs i) = Zmod.unsigned (N.v3764 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3764 s i)) at 1.
  unfold R.v3764, N.v3764.
  rewrite ?node_3763.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1621_nr_5F1627.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1621_nr_5F1627 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3765 (s : N.State) (i : N.Inputs) :
  R.v3765 (state s) (inputs i) = Zmod.unsigned (N.v3765 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3765 s i)) at 1.
  unfold R.v3765, N.v3765.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3766 (s : N.State) (i : N.Inputs) :
  R.v3766 (state s) (inputs i) = Zmod.unsigned (N.v3766 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3766 s i)) at 1.
  unfold R.v3766, N.v3766.
  rewrite ?node_3765.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1622_nr_5F1628.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1622_nr_5F1628 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3767 (s : N.State) (i : N.Inputs) :
  R.v3767 (state s) (inputs i) = Zmod.unsigned (N.v3767 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3767 s i)) at 1.
  unfold R.v3767, N.v3767.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3768 (s : N.State) (i : N.Inputs) :
  R.v3768 (state s) (inputs i) = Zmod.unsigned (N.v3768 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3768 s i)) at 1.
  unfold R.v3768, N.v3768.
  rewrite ?node_3767.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1623_nr_5F1629.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1623_nr_5F1629 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3769 (s : N.State) (i : N.Inputs) :
  R.v3769 (state s) (inputs i) = Zmod.unsigned (N.v3769 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3769 s i)) at 1.
  unfold R.v3769, N.v3769.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3770 (s : N.State) (i : N.Inputs) :
  R.v3770 (state s) (inputs i) = Zmod.unsigned (N.v3770 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3770 s i)) at 1.
  unfold R.v3770, N.v3770.
  rewrite ?node_3769.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1624_nr_5F1630.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1624_nr_5F1630 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3771 (s : N.State) (i : N.Inputs) :
  R.v3771 (state s) (inputs i) = Zmod.unsigned (N.v3771 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3771 s i)) at 1.
  unfold R.v3771, N.v3771.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3772 (s : N.State) (i : N.Inputs) :
  R.v3772 (state s) (inputs i) = Zmod.unsigned (N.v3772 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3772 s i)) at 1.
  unfold R.v3772, N.v3772.
  rewrite ?node_3771.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1625_nr_5F1631.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1625_nr_5F1631 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3773 (s : N.State) (i : N.Inputs) :
  R.v3773 (state s) (inputs i) = Zmod.unsigned (N.v3773 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3773 s i)) at 1.
  unfold R.v3773, N.v3773.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3774 (s : N.State) (i : N.Inputs) :
  R.v3774 (state s) (inputs i) = Zmod.unsigned (N.v3774 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3774 s i)) at 1.
  unfold R.v3774, N.v3774.
  rewrite ?node_3773.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1626_nr_5F1632.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1626_nr_5F1632 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3775 (s : N.State) (i : N.Inputs) :
  R.v3775 (state s) (inputs i) = Zmod.unsigned (N.v3775 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3775 s i)) at 1.
  unfold R.v3775, N.v3775.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3776 (s : N.State) (i : N.Inputs) :
  R.v3776 (state s) (inputs i) = Zmod.unsigned (N.v3776 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3776 s i)) at 1.
  unfold R.v3776, N.v3776.
  rewrite ?node_3775.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1627_nr_5F1633.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1627_nr_5F1633 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3777 (s : N.State) (i : N.Inputs) :
  R.v3777 (state s) (inputs i) = Zmod.unsigned (N.v3777 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3777 s i)) at 1.
  unfold R.v3777, N.v3777.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3778 (s : N.State) (i : N.Inputs) :
  R.v3778 (state s) (inputs i) = Zmod.unsigned (N.v3778 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3778 s i)) at 1.
  unfold R.v3778, N.v3778.
  rewrite ?node_3777.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1628_nr_5F1634.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1628_nr_5F1634 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3779 (s : N.State) (i : N.Inputs) :
  R.v3779 (state s) (inputs i) = Zmod.unsigned (N.v3779 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3779 s i)) at 1.
  unfold R.v3779, N.v3779.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3780 (s : N.State) (i : N.Inputs) :
  R.v3780 (state s) (inputs i) = Zmod.unsigned (N.v3780 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3780 s i)) at 1.
  unfold R.v3780, N.v3780.
  rewrite ?node_3779.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1629_nr_5F1636.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1629_nr_5F1636 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3781 (s : N.State) (i : N.Inputs) :
  R.v3781 (state s) (inputs i) = Zmod.unsigned (N.v3781 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3781 s i)) at 1.
  unfold R.v3781, N.v3781.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3782 (s : N.State) (i : N.Inputs) :
  R.v3782 (state s) (inputs i) = Zmod.unsigned (N.v3782 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3782 s i)) at 1.
  unfold R.v3782, N.v3782.
  rewrite ?node_3781.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1630_nr_5F1637.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1630_nr_5F1637 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3783 (s : N.State) (i : N.Inputs) :
  R.v3783 (state s) (inputs i) = Zmod.unsigned (N.v3783 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3783 s i)) at 1.
  unfold R.v3783, N.v3783.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3784 (s : N.State) (i : N.Inputs) :
  R.v3784 (state s) (inputs i) = Zmod.unsigned (N.v3784 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3784 s i)) at 1.
  unfold R.v3784, N.v3784.
  rewrite ?node_3783.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1631_nr_5F1638.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1631_nr_5F1638 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3785 (s : N.State) (i : N.Inputs) :
  R.v3785 (state s) (inputs i) = Zmod.unsigned (N.v3785 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3785 s i)) at 1.
  unfold R.v3785, N.v3785.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3786 (s : N.State) (i : N.Inputs) :
  R.v3786 (state s) (inputs i) = Zmod.unsigned (N.v3786 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3786 s i)) at 1.
  unfold R.v3786, N.v3786.
  rewrite ?node_3785.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1632_nr_5F1639.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1632_nr_5F1639 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3787 (s : N.State) (i : N.Inputs) :
  R.v3787 (state s) (inputs i) = Zmod.unsigned (N.v3787 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3787 s i)) at 1.
  unfold R.v3787, N.v3787.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3788 (s : N.State) (i : N.Inputs) :
  R.v3788 (state s) (inputs i) = Zmod.unsigned (N.v3788 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3788 s i)) at 1.
  unfold R.v3788, N.v3788.
  rewrite ?node_3787.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1633_nr_5F1640.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1633_nr_5F1640 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3789 (s : N.State) (i : N.Inputs) :
  R.v3789 (state s) (inputs i) = Zmod.unsigned (N.v3789 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3789 s i)) at 1.
  unfold R.v3789, N.v3789.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3790 (s : N.State) (i : N.Inputs) :
  R.v3790 (state s) (inputs i) = Zmod.unsigned (N.v3790 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3790 s i)) at 1.
  unfold R.v3790, N.v3790.
  rewrite ?node_3789.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1634_nr_5F1641.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1634_nr_5F1641 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3791 (s : N.State) (i : N.Inputs) :
  R.v3791 (state s) (inputs i) = Zmod.unsigned (N.v3791 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3791 s i)) at 1.
  unfold R.v3791, N.v3791.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3792 (s : N.State) (i : N.Inputs) :
  R.v3792 (state s) (inputs i) = Zmod.unsigned (N.v3792 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3792 s i)) at 1.
  unfold R.v3792, N.v3792.
  rewrite ?node_3791.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1635_nr_5F1642.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1635_nr_5F1642 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3793 (s : N.State) (i : N.Inputs) :
  R.v3793 (state s) (inputs i) = Zmod.unsigned (N.v3793 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3793 s i)) at 1.
  unfold R.v3793, N.v3793.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3794 (s : N.State) (i : N.Inputs) :
  R.v3794 (state s) (inputs i) = Zmod.unsigned (N.v3794 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3794 s i)) at 1.
  unfold R.v3794, N.v3794.
  rewrite ?node_3793.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1636_nr_5F1643.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1636_nr_5F1643 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3795 (s : N.State) (i : N.Inputs) :
  R.v3795 (state s) (inputs i) = Zmod.unsigned (N.v3795 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3795 s i)) at 1.
  unfold R.v3795, N.v3795.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3796 (s : N.State) (i : N.Inputs) :
  R.v3796 (state s) (inputs i) = Zmod.unsigned (N.v3796 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3796 s i)) at 1.
  unfold R.v3796, N.v3796.
  rewrite ?node_3795.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1637_nr_5F1644.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1637_nr_5F1644 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3797 (s : N.State) (i : N.Inputs) :
  R.v3797 (state s) (inputs i) = Zmod.unsigned (N.v3797 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3797 s i)) at 1.
  unfold R.v3797, N.v3797.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3798 (s : N.State) (i : N.Inputs) :
  R.v3798 (state s) (inputs i) = Zmod.unsigned (N.v3798 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3798 s i)) at 1.
  unfold R.v3798, N.v3798.
  rewrite ?node_3797.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1638_nr_5F1645.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1638_nr_5F1645 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3799 (s : N.State) (i : N.Inputs) :
  R.v3799 (state s) (inputs i) = Zmod.unsigned (N.v3799 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3799 s i)) at 1.
  unfold R.v3799, N.v3799.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3800 (s : N.State) (i : N.Inputs) :
  R.v3800 (state s) (inputs i) = Zmod.unsigned (N.v3800 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3800 s i)) at 1.
  unfold R.v3800, N.v3800.
  rewrite ?node_3799.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1639_nr_5F1646.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1639_nr_5F1646 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3801 (s : N.State) (i : N.Inputs) :
  R.v3801 (state s) (inputs i) = Zmod.unsigned (N.v3801 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3801 s i)) at 1.
  unfold R.v3801, N.v3801.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3802 (s : N.State) (i : N.Inputs) :
  R.v3802 (state s) (inputs i) = Zmod.unsigned (N.v3802 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3802 s i)) at 1.
  unfold R.v3802, N.v3802.
  rewrite ?node_3801.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1640_nr_5F1647.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1640_nr_5F1647 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3803 (s : N.State) (i : N.Inputs) :
  R.v3803 (state s) (inputs i) = Zmod.unsigned (N.v3803 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3803 s i)) at 1.
  unfold R.v3803, N.v3803.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3804 (s : N.State) (i : N.Inputs) :
  R.v3804 (state s) (inputs i) = Zmod.unsigned (N.v3804 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3804 s i)) at 1.
  unfold R.v3804, N.v3804.
  rewrite ?node_3803.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1641_nr_5F1648.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1641_nr_5F1648 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3805 (s : N.State) (i : N.Inputs) :
  R.v3805 (state s) (inputs i) = Zmod.unsigned (N.v3805 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3805 s i)) at 1.
  unfold R.v3805, N.v3805.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3806 (s : N.State) (i : N.Inputs) :
  R.v3806 (state s) (inputs i) = Zmod.unsigned (N.v3806 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3806 s i)) at 1.
  unfold R.v3806, N.v3806.
  rewrite ?node_3805.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1642_nr_5F1649.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1642_nr_5F1649 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3807 (s : N.State) (i : N.Inputs) :
  R.v3807 (state s) (inputs i) = Zmod.unsigned (N.v3807 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3807 s i)) at 1.
  unfold R.v3807, N.v3807.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3808 (s : N.State) (i : N.Inputs) :
  R.v3808 (state s) (inputs i) = Zmod.unsigned (N.v3808 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3808 s i)) at 1.
  unfold R.v3808, N.v3808.
  rewrite ?node_3807.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1643_nr_5F1650.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1643_nr_5F1650 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3809 (s : N.State) (i : N.Inputs) :
  R.v3809 (state s) (inputs i) = Zmod.unsigned (N.v3809 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3809 s i)) at 1.
  unfold R.v3809, N.v3809.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3810 (s : N.State) (i : N.Inputs) :
  R.v3810 (state s) (inputs i) = Zmod.unsigned (N.v3810 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3810 s i)) at 1.
  unfold R.v3810, N.v3810.
  rewrite ?node_3809.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1644_nr_5F1651.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1644_nr_5F1651 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3811 (s : N.State) (i : N.Inputs) :
  R.v3811 (state s) (inputs i) = Zmod.unsigned (N.v3811 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3811 s i)) at 1.
  unfold R.v3811, N.v3811.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3812 (s : N.State) (i : N.Inputs) :
  R.v3812 (state s) (inputs i) = Zmod.unsigned (N.v3812 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3812 s i)) at 1.
  unfold R.v3812, N.v3812.
  rewrite ?node_3811.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1645_nr_5F1652.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1645_nr_5F1652 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3813 (s : N.State) (i : N.Inputs) :
  R.v3813 (state s) (inputs i) = Zmod.unsigned (N.v3813 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3813 s i)) at 1.
  unfold R.v3813, N.v3813.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3814 (s : N.State) (i : N.Inputs) :
  R.v3814 (state s) (inputs i) = Zmod.unsigned (N.v3814 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3814 s i)) at 1.
  unfold R.v3814, N.v3814.
  rewrite ?node_3813.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1646_nr_5F1653.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1646_nr_5F1653 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3815 (s : N.State) (i : N.Inputs) :
  R.v3815 (state s) (inputs i) = Zmod.unsigned (N.v3815 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3815 s i)) at 1.
  unfold R.v3815, N.v3815.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3816 (s : N.State) (i : N.Inputs) :
  R.v3816 (state s) (inputs i) = Zmod.unsigned (N.v3816 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3816 s i)) at 1.
  unfold R.v3816, N.v3816.
  rewrite ?node_3815.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1647_nr_5F1654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1647_nr_5F1654 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3817 (s : N.State) (i : N.Inputs) :
  R.v3817 (state s) (inputs i) = Zmod.unsigned (N.v3817 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3817 s i)) at 1.
  unfold R.v3817, N.v3817.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3818 (s : N.State) (i : N.Inputs) :
  R.v3818 (state s) (inputs i) = Zmod.unsigned (N.v3818 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3818 s i)) at 1.
  unfold R.v3818, N.v3818.
  rewrite ?node_3817.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1648_nr_5F1655.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1648_nr_5F1655 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3819 (s : N.State) (i : N.Inputs) :
  R.v3819 (state s) (inputs i) = Zmod.unsigned (N.v3819 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3819 s i)) at 1.
  unfold R.v3819, N.v3819.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3820 (s : N.State) (i : N.Inputs) :
  R.v3820 (state s) (inputs i) = Zmod.unsigned (N.v3820 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3820 s i)) at 1.
  unfold R.v3820, N.v3820.
  rewrite ?node_3819.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1649_nr_5F1656.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1649_nr_5F1656 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3821 (s : N.State) (i : N.Inputs) :
  R.v3821 (state s) (inputs i) = Zmod.unsigned (N.v3821 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3821 s i)) at 1.
  unfold R.v3821, N.v3821.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3822 (s : N.State) (i : N.Inputs) :
  R.v3822 (state s) (inputs i) = Zmod.unsigned (N.v3822 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3822 s i)) at 1.
  unfold R.v3822, N.v3822.
  rewrite ?node_3821.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1650_nr_5F1657.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1650_nr_5F1657 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3823 (s : N.State) (i : N.Inputs) :
  R.v3823 (state s) (inputs i) = Zmod.unsigned (N.v3823 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3823 s i)) at 1.
  unfold R.v3823, N.v3823.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3824 (s : N.State) (i : N.Inputs) :
  R.v3824 (state s) (inputs i) = Zmod.unsigned (N.v3824 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3824 s i)) at 1.
  unfold R.v3824, N.v3824.
  rewrite ?node_3823.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1651_nr_5F1658.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1651_nr_5F1658 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3825 (s : N.State) (i : N.Inputs) :
  R.v3825 (state s) (inputs i) = Zmod.unsigned (N.v3825 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3825 s i)) at 1.
  unfold R.v3825, N.v3825.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3826 (s : N.State) (i : N.Inputs) :
  R.v3826 (state s) (inputs i) = Zmod.unsigned (N.v3826 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3826 s i)) at 1.
  unfold R.v3826, N.v3826.
  rewrite ?node_3825.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1652_nr_5F1659.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1652_nr_5F1659 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3827 (s : N.State) (i : N.Inputs) :
  R.v3827 (state s) (inputs i) = Zmod.unsigned (N.v3827 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3827 s i)) at 1.
  unfold R.v3827, N.v3827.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3828 (s : N.State) (i : N.Inputs) :
  R.v3828 (state s) (inputs i) = Zmod.unsigned (N.v3828 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3828 s i)) at 1.
  unfold R.v3828, N.v3828.
  rewrite ?node_3827.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1653_nr_5F1660.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1653_nr_5F1660 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3829 (s : N.State) (i : N.Inputs) :
  R.v3829 (state s) (inputs i) = Zmod.unsigned (N.v3829 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3829 s i)) at 1.
  unfold R.v3829, N.v3829.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3830 (s : N.State) (i : N.Inputs) :
  R.v3830 (state s) (inputs i) = Zmod.unsigned (N.v3830 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3830 s i)) at 1.
  unfold R.v3830, N.v3830.
  unfold R.v3021, N.v3021.
  rewrite ?node_3829.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3831 (s : N.State) (i : N.Inputs) :
  R.v3831 (state s) (inputs i) = Zmod.unsigned (N.v3831 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3831 s i)) at 1.
  unfold R.v3831, N.v3831.
  rewrite ?node_3830.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1654_nr_5F1661.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1654_nr_5F1661 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3832 (s : N.State) (i : N.Inputs) :
  R.v3832 (state s) (inputs i) = Zmod.unsigned (N.v3832 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3832 s i)) at 1.
  unfold R.v3832, N.v3832.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3833 (s : N.State) (i : N.Inputs) :
  R.v3833 (state s) (inputs i) = Zmod.unsigned (N.v3833 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3833 s i)) at 1.
  unfold R.v3833, N.v3833.
  rewrite ?node_3832.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1655_nr_5F1662.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1655_nr_5F1662 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3834 (s : N.State) (i : N.Inputs) :
  R.v3834 (state s) (inputs i) = Zmod.unsigned (N.v3834 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3834 s i)) at 1.
  unfold R.v3834, N.v3834.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3835 (s : N.State) (i : N.Inputs) :
  R.v3835 (state s) (inputs i) = Zmod.unsigned (N.v3835 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3835 s i)) at 1.
  unfold R.v3835, N.v3835.
  rewrite ?node_3834.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1656_nr_5F1663.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1656_nr_5F1663 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3836 (s : N.State) (i : N.Inputs) :
  R.v3836 (state s) (inputs i) = Zmod.unsigned (N.v3836 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3836 s i)) at 1.
  unfold R.v3836, N.v3836.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3837 (s : N.State) (i : N.Inputs) :
  R.v3837 (state s) (inputs i) = Zmod.unsigned (N.v3837 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3837 s i)) at 1.
  unfold R.v3837, N.v3837.
  rewrite ?node_3836.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1657_nr_5F1664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1657_nr_5F1664 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3838 (s : N.State) (i : N.Inputs) :
  R.v3838 (state s) (inputs i) = Zmod.unsigned (N.v3838 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3838 s i)) at 1.
  unfold R.v3838, N.v3838.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3839 (s : N.State) (i : N.Inputs) :
  R.v3839 (state s) (inputs i) = Zmod.unsigned (N.v3839 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3839 s i)) at 1.
  unfold R.v3839, N.v3839.
  rewrite ?node_3838.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1658_nr_5F1665.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1658_nr_5F1665 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3840 (s : N.State) (i : N.Inputs) :
  R.v3840 (state s) (inputs i) = Zmod.unsigned (N.v3840 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3840 s i)) at 1.
  unfold R.v3840, N.v3840.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3841 (s : N.State) (i : N.Inputs) :
  R.v3841 (state s) (inputs i) = Zmod.unsigned (N.v3841 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3841 s i)) at 1.
  unfold R.v3841, N.v3841.
  rewrite ?node_3840.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1659_nr_5F1666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1659_nr_5F1666 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3842 (s : N.State) (i : N.Inputs) :
  R.v3842 (state s) (inputs i) = Zmod.unsigned (N.v3842 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3842 s i)) at 1.
  unfold R.v3842, N.v3842.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3843 (s : N.State) (i : N.Inputs) :
  R.v3843 (state s) (inputs i) = Zmod.unsigned (N.v3843 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3843 s i)) at 1.
  unfold R.v3843, N.v3843.
  rewrite ?node_3842.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1660_nr_5F1667.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1660_nr_5F1667 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3844 (s : N.State) (i : N.Inputs) :
  R.v3844 (state s) (inputs i) = Zmod.unsigned (N.v3844 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3844 s i)) at 1.
  unfold R.v3844, N.v3844.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3845 (s : N.State) (i : N.Inputs) :
  R.v3845 (state s) (inputs i) = Zmod.unsigned (N.v3845 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3845 s i)) at 1.
  unfold R.v3845, N.v3845.
  rewrite ?node_3844.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1661_nr_5F1668.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1661_nr_5F1668 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3846 (s : N.State) (i : N.Inputs) :
  R.v3846 (state s) (inputs i) = Zmod.unsigned (N.v3846 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3846 s i)) at 1.
  unfold R.v3846, N.v3846.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3847 (s : N.State) (i : N.Inputs) :
  R.v3847 (state s) (inputs i) = Zmod.unsigned (N.v3847 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3847 s i)) at 1.
  unfold R.v3847, N.v3847.
  rewrite ?node_3846.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1662_nr_5F1669.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1662_nr_5F1669 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3848 (s : N.State) (i : N.Inputs) :
  R.v3848 (state s) (inputs i) = Zmod.unsigned (N.v3848 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3848 s i)) at 1.
  unfold R.v3848, N.v3848.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3849 (s : N.State) (i : N.Inputs) :
  R.v3849 (state s) (inputs i) = Zmod.unsigned (N.v3849 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3849 s i)) at 1.
  unfold R.v3849, N.v3849.
  rewrite ?node_3848.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1663_nr_5F1670.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1663_nr_5F1670 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3850 (s : N.State) (i : N.Inputs) :
  R.v3850 (state s) (inputs i) = Zmod.unsigned (N.v3850 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3850 s i)) at 1.
  unfold R.v3850, N.v3850.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3851 (s : N.State) (i : N.Inputs) :
  R.v3851 (state s) (inputs i) = Zmod.unsigned (N.v3851 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3851 s i)) at 1.
  unfold R.v3851, N.v3851.
  rewrite ?node_3850.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1664_nr_5F1671.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1664_nr_5F1671 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3852 (s : N.State) (i : N.Inputs) :
  R.v3852 (state s) (inputs i) = Zmod.unsigned (N.v3852 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3852 s i)) at 1.
  unfold R.v3852, N.v3852.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3853 (s : N.State) (i : N.Inputs) :
  R.v3853 (state s) (inputs i) = Zmod.unsigned (N.v3853 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3853 s i)) at 1.
  unfold R.v3853, N.v3853.
  rewrite ?node_3852.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1665_nr_5F1672.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1665_nr_5F1672 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3854 (s : N.State) (i : N.Inputs) :
  R.v3854 (state s) (inputs i) = Zmod.unsigned (N.v3854 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3854 s i)) at 1.
  unfold R.v3854, N.v3854.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3855 (s : N.State) (i : N.Inputs) :
  R.v3855 (state s) (inputs i) = Zmod.unsigned (N.v3855 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3855 s i)) at 1.
  unfold R.v3855, N.v3855.
  rewrite ?node_3854.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1666_nr_5F1673.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1666_nr_5F1673 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3856 (s : N.State) (i : N.Inputs) :
  R.v3856 (state s) (inputs i) = Zmod.unsigned (N.v3856 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3856 s i)) at 1.
  unfold R.v3856, N.v3856.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3857 (s : N.State) (i : N.Inputs) :
  R.v3857 (state s) (inputs i) = Zmod.unsigned (N.v3857 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3857 s i)) at 1.
  unfold R.v3857, N.v3857.
  rewrite ?node_3856.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1667_nr_5F1674.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1667_nr_5F1674 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3858 (s : N.State) (i : N.Inputs) :
  R.v3858 (state s) (inputs i) = Zmod.unsigned (N.v3858 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3858 s i)) at 1.
  unfold R.v3858, N.v3858.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3859 (s : N.State) (i : N.Inputs) :
  R.v3859 (state s) (inputs i) = Zmod.unsigned (N.v3859 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3859 s i)) at 1.
  unfold R.v3859, N.v3859.
  rewrite ?node_3858.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1668_nr_5F1675.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1668_nr_5F1675 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3860 (s : N.State) (i : N.Inputs) :
  R.v3860 (state s) (inputs i) = Zmod.unsigned (N.v3860 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3860 s i)) at 1.
  unfold R.v3860, N.v3860.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3861 (s : N.State) (i : N.Inputs) :
  R.v3861 (state s) (inputs i) = Zmod.unsigned (N.v3861 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3861 s i)) at 1.
  unfold R.v3861, N.v3861.
  rewrite ?node_3860.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1669_nr_5F1676.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1669_nr_5F1676 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3862 (s : N.State) (i : N.Inputs) :
  R.v3862 (state s) (inputs i) = Zmod.unsigned (N.v3862 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3862 s i)) at 1.
  unfold R.v3862, N.v3862.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3863 (s : N.State) (i : N.Inputs) :
  R.v3863 (state s) (inputs i) = Zmod.unsigned (N.v3863 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3863 s i)) at 1.
  unfold R.v3863, N.v3863.
  rewrite ?node_3862.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1670_nr_5F1677.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1670_nr_5F1677 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3864 (s : N.State) (i : N.Inputs) :
  R.v3864 (state s) (inputs i) = Zmod.unsigned (N.v3864 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3864 s i)) at 1.
  unfold R.v3864, N.v3864.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3865 (s : N.State) (i : N.Inputs) :
  R.v3865 (state s) (inputs i) = Zmod.unsigned (N.v3865 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3865 s i)) at 1.
  unfold R.v3865, N.v3865.
  rewrite ?node_3864.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1671_nr_5F1678.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1671_nr_5F1678 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3866 (s : N.State) (i : N.Inputs) :
  R.v3866 (state s) (inputs i) = Zmod.unsigned (N.v3866 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3866 s i)) at 1.
  unfold R.v3866, N.v3866.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3867 (s : N.State) (i : N.Inputs) :
  R.v3867 (state s) (inputs i) = Zmod.unsigned (N.v3867 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3867 s i)) at 1.
  unfold R.v3867, N.v3867.
  rewrite ?node_3866.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1672_nr_5F1679.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1672_nr_5F1679 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3868 (s : N.State) (i : N.Inputs) :
  R.v3868 (state s) (inputs i) = Zmod.unsigned (N.v3868 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3868 s i)) at 1.
  unfold R.v3868, N.v3868.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3869 (s : N.State) (i : N.Inputs) :
  R.v3869 (state s) (inputs i) = Zmod.unsigned (N.v3869 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3869 s i)) at 1.
  unfold R.v3869, N.v3869.
  rewrite ?node_3868.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1673_nr_5F1680.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1673_nr_5F1680 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3870 (s : N.State) (i : N.Inputs) :
  R.v3870 (state s) (inputs i) = Zmod.unsigned (N.v3870 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3870 s i)) at 1.
  unfold R.v3870, N.v3870.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3871 (s : N.State) (i : N.Inputs) :
  R.v3871 (state s) (inputs i) = Zmod.unsigned (N.v3871 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3871 s i)) at 1.
  unfold R.v3871, N.v3871.
  rewrite ?node_3870.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1674_nr_5F1681.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1674_nr_5F1681 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3872 (s : N.State) (i : N.Inputs) :
  R.v3872 (state s) (inputs i) = Zmod.unsigned (N.v3872 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3872 s i)) at 1.
  unfold R.v3872, N.v3872.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3873 (s : N.State) (i : N.Inputs) :
  R.v3873 (state s) (inputs i) = Zmod.unsigned (N.v3873 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3873 s i)) at 1.
  unfold R.v3873, N.v3873.
  rewrite ?node_3872.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1675_nr_5F1682.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1675_nr_5F1682 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3874 (s : N.State) (i : N.Inputs) :
  R.v3874 (state s) (inputs i) = Zmod.unsigned (N.v3874 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3874 s i)) at 1.
  unfold R.v3874, N.v3874.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3875 (s : N.State) (i : N.Inputs) :
  R.v3875 (state s) (inputs i) = Zmod.unsigned (N.v3875 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3875 s i)) at 1.
  unfold R.v3875, N.v3875.
  rewrite ?node_3874.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1676_nr_5F1683.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1676_nr_5F1683 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3876 (s : N.State) (i : N.Inputs) :
  R.v3876 (state s) (inputs i) = Zmod.unsigned (N.v3876 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3876 s i)) at 1.
  unfold R.v3876, N.v3876.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3877 (s : N.State) (i : N.Inputs) :
  R.v3877 (state s) (inputs i) = Zmod.unsigned (N.v3877 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3877 s i)) at 1.
  unfold R.v3877, N.v3877.
  rewrite ?node_3876.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1677_nr_5F1684.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1677_nr_5F1684 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3878 (s : N.State) (i : N.Inputs) :
  R.v3878 (state s) (inputs i) = Zmod.unsigned (N.v3878 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3878 s i)) at 1.
  unfold R.v3878, N.v3878.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3879 (s : N.State) (i : N.Inputs) :
  R.v3879 (state s) (inputs i) = Zmod.unsigned (N.v3879 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3879 s i)) at 1.
  unfold R.v3879, N.v3879.
  rewrite ?node_3878.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1678_nr_5F1685.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1678_nr_5F1685 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3880 (s : N.State) (i : N.Inputs) :
  R.v3880 (state s) (inputs i) = Zmod.unsigned (N.v3880 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3880 s i)) at 1.
  unfold R.v3880, N.v3880.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3881 (s : N.State) (i : N.Inputs) :
  R.v3881 (state s) (inputs i) = Zmod.unsigned (N.v3881 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3881 s i)) at 1.
  unfold R.v3881, N.v3881.
  rewrite ?node_3880.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1679_nr_5F1687.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1679_nr_5F1687 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3882 (s : N.State) (i : N.Inputs) :
  R.v3882 (state s) (inputs i) = Zmod.unsigned (N.v3882 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3882 s i)) at 1.
  unfold R.v3882, N.v3882.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3883 (s : N.State) (i : N.Inputs) :
  R.v3883 (state s) (inputs i) = Zmod.unsigned (N.v3883 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3883 s i)) at 1.
  unfold R.v3883, N.v3883.
  rewrite ?node_3882.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1680_nr_5F1688.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1680_nr_5F1688 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3884 (s : N.State) (i : N.Inputs) :
  R.v3884 (state s) (inputs i) = Zmod.unsigned (N.v3884 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3884 s i)) at 1.
  unfold R.v3884, N.v3884.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3885 (s : N.State) (i : N.Inputs) :
  R.v3885 (state s) (inputs i) = Zmod.unsigned (N.v3885 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3885 s i)) at 1.
  unfold R.v3885, N.v3885.
  rewrite ?node_3884.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1681_nr_5F1689.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1681_nr_5F1689 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3886 (s : N.State) (i : N.Inputs) :
  R.v3886 (state s) (inputs i) = Zmod.unsigned (N.v3886 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3886 s i)) at 1.
  unfold R.v3886, N.v3886.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3887 (s : N.State) (i : N.Inputs) :
  R.v3887 (state s) (inputs i) = Zmod.unsigned (N.v3887 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3887 s i)) at 1.
  unfold R.v3887, N.v3887.
  rewrite ?node_3886.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1682_nr_5F1690.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1682_nr_5F1690 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3888 (s : N.State) (i : N.Inputs) :
  R.v3888 (state s) (inputs i) = Zmod.unsigned (N.v3888 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3888 s i)) at 1.
  unfold R.v3888, N.v3888.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3889 (s : N.State) (i : N.Inputs) :
  R.v3889 (state s) (inputs i) = Zmod.unsigned (N.v3889 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3889 s i)) at 1.
  unfold R.v3889, N.v3889.
  rewrite ?node_3888.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1683_nr_5F1691.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1683_nr_5F1691 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3890 (s : N.State) (i : N.Inputs) :
  R.v3890 (state s) (inputs i) = Zmod.unsigned (N.v3890 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3890 s i)) at 1.
  unfold R.v3890, N.v3890.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3891 (s : N.State) (i : N.Inputs) :
  R.v3891 (state s) (inputs i) = Zmod.unsigned (N.v3891 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3891 s i)) at 1.
  unfold R.v3891, N.v3891.
  rewrite ?node_3890.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1684_nr_5F1692.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1684_nr_5F1692 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3892 (s : N.State) (i : N.Inputs) :
  R.v3892 (state s) (inputs i) = Zmod.unsigned (N.v3892 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3892 s i)) at 1.
  unfold R.v3892, N.v3892.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3893 (s : N.State) (i : N.Inputs) :
  R.v3893 (state s) (inputs i) = Zmod.unsigned (N.v3893 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3893 s i)) at 1.
  unfold R.v3893, N.v3893.
  rewrite ?node_3892.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1685_nr_5F1693.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1685_nr_5F1693 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3894 (s : N.State) (i : N.Inputs) :
  R.v3894 (state s) (inputs i) = Zmod.unsigned (N.v3894 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3894 s i)) at 1.
  unfold R.v3894, N.v3894.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3895 (s : N.State) (i : N.Inputs) :
  R.v3895 (state s) (inputs i) = Zmod.unsigned (N.v3895 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3895 s i)) at 1.
  unfold R.v3895, N.v3895.
  rewrite ?node_3894.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1686_nr_5F1694.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1686_nr_5F1694 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3896 (s : N.State) (i : N.Inputs) :
  R.v3896 (state s) (inputs i) = Zmod.unsigned (N.v3896 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3896 s i)) at 1.
  unfold R.v3896, N.v3896.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3897 (s : N.State) (i : N.Inputs) :
  R.v3897 (state s) (inputs i) = Zmod.unsigned (N.v3897 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3897 s i)) at 1.
  unfold R.v3897, N.v3897.
  rewrite ?node_3896.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1687_nr_5F1695.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1687_nr_5F1695 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3898 (s : N.State) (i : N.Inputs) :
  R.v3898 (state s) (inputs i) = Zmod.unsigned (N.v3898 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3898 s i)) at 1.
  unfold R.v3898, N.v3898.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3899 (s : N.State) (i : N.Inputs) :
  R.v3899 (state s) (inputs i) = Zmod.unsigned (N.v3899 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3899 s i)) at 1.
  unfold R.v3899, N.v3899.
  rewrite ?node_3898.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1688_nr_5F1696.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1688_nr_5F1696 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3900 (s : N.State) (i : N.Inputs) :
  R.v3900 (state s) (inputs i) = Zmod.unsigned (N.v3900 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3900 s i)) at 1.
  unfold R.v3900, N.v3900.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3901 (s : N.State) (i : N.Inputs) :
  R.v3901 (state s) (inputs i) = Zmod.unsigned (N.v3901 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3901 s i)) at 1.
  unfold R.v3901, N.v3901.
  rewrite ?node_3900.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1689_nr_5F1697.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1689_nr_5F1697 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3902 (s : N.State) (i : N.Inputs) :
  R.v3902 (state s) (inputs i) = Zmod.unsigned (N.v3902 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3902 s i)) at 1.
  unfold R.v3902, N.v3902.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3903 (s : N.State) (i : N.Inputs) :
  R.v3903 (state s) (inputs i) = Zmod.unsigned (N.v3903 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3903 s i)) at 1.
  unfold R.v3903, N.v3903.
  rewrite ?node_3902.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1690_nr_5F1698.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1690_nr_5F1698 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3904 (s : N.State) (i : N.Inputs) :
  R.v3904 (state s) (inputs i) = Zmod.unsigned (N.v3904 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3904 s i)) at 1.
  unfold R.v3904, N.v3904.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3905 (s : N.State) (i : N.Inputs) :
  R.v3905 (state s) (inputs i) = Zmod.unsigned (N.v3905 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3905 s i)) at 1.
  unfold R.v3905, N.v3905.
  rewrite ?node_3904.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1691_nr_5F1699.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1691_nr_5F1699 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3906 (s : N.State) (i : N.Inputs) :
  R.v3906 (state s) (inputs i) = Zmod.unsigned (N.v3906 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3906 s i)) at 1.
  unfold R.v3906, N.v3906.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3907 (s : N.State) (i : N.Inputs) :
  R.v3907 (state s) (inputs i) = Zmod.unsigned (N.v3907 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3907 s i)) at 1.
  unfold R.v3907, N.v3907.
  rewrite ?node_3906.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1692_nr_5F1700.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1692_nr_5F1700 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3908 (s : N.State) (i : N.Inputs) :
  R.v3908 (state s) (inputs i) = Zmod.unsigned (N.v3908 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3908 s i)) at 1.
  unfold R.v3908, N.v3908.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3909 (s : N.State) (i : N.Inputs) :
  R.v3909 (state s) (inputs i) = Zmod.unsigned (N.v3909 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3909 s i)) at 1.
  unfold R.v3909, N.v3909.
  rewrite ?node_3908.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1693_nr_5F1701.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1693_nr_5F1701 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3910 (s : N.State) (i : N.Inputs) :
  R.v3910 (state s) (inputs i) = Zmod.unsigned (N.v3910 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3910 s i)) at 1.
  unfold R.v3910, N.v3910.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3911 (s : N.State) (i : N.Inputs) :
  R.v3911 (state s) (inputs i) = Zmod.unsigned (N.v3911 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3911 s i)) at 1.
  unfold R.v3911, N.v3911.
  rewrite ?node_3910.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1694_nr_5F1702.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1694_nr_5F1702 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3912 (s : N.State) (i : N.Inputs) :
  R.v3912 (state s) (inputs i) = Zmod.unsigned (N.v3912 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3912 s i)) at 1.
  unfold R.v3912, N.v3912.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3913 (s : N.State) (i : N.Inputs) :
  R.v3913 (state s) (inputs i) = Zmod.unsigned (N.v3913 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3913 s i)) at 1.
  unfold R.v3913, N.v3913.
  rewrite ?node_3912.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1695_nr_5F1703.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1695_nr_5F1703 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3914 (s : N.State) (i : N.Inputs) :
  R.v3914 (state s) (inputs i) = Zmod.unsigned (N.v3914 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3914 s i)) at 1.
  unfold R.v3914, N.v3914.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3915 (s : N.State) (i : N.Inputs) :
  R.v3915 (state s) (inputs i) = Zmod.unsigned (N.v3915 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3915 s i)) at 1.
  unfold R.v3915, N.v3915.
  rewrite ?node_3914.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1696_nr_5F1704.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1696_nr_5F1704 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3916 (s : N.State) (i : N.Inputs) :
  R.v3916 (state s) (inputs i) = Zmod.unsigned (N.v3916 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3916 s i)) at 1.
  unfold R.v3916, N.v3916.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3917 (s : N.State) (i : N.Inputs) :
  R.v3917 (state s) (inputs i) = Zmod.unsigned (N.v3917 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3917 s i)) at 1.
  unfold R.v3917, N.v3917.
  rewrite ?node_3916.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1697_nr_5F1705.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1697_nr_5F1705 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3918 (s : N.State) (i : N.Inputs) :
  R.v3918 (state s) (inputs i) = Zmod.unsigned (N.v3918 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3918 s i)) at 1.
  unfold R.v3918, N.v3918.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3919 (s : N.State) (i : N.Inputs) :
  R.v3919 (state s) (inputs i) = Zmod.unsigned (N.v3919 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3919 s i)) at 1.
  unfold R.v3919, N.v3919.
  rewrite ?node_3918.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1698_nr_5F1706.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1698_nr_5F1706 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3920 (s : N.State) (i : N.Inputs) :
  R.v3920 (state s) (inputs i) = Zmod.unsigned (N.v3920 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3920 s i)) at 1.
  unfold R.v3920, N.v3920.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3921 (s : N.State) (i : N.Inputs) :
  R.v3921 (state s) (inputs i) = Zmod.unsigned (N.v3921 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3921 s i)) at 1.
  unfold R.v3921, N.v3921.
  rewrite ?node_3920.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1699_nr_5F1707.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1699_nr_5F1707 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3922 (s : N.State) (i : N.Inputs) :
  R.v3922 (state s) (inputs i) = Zmod.unsigned (N.v3922 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3922 s i)) at 1.
  unfold R.v3922, N.v3922.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3923 (s : N.State) (i : N.Inputs) :
  R.v3923 (state s) (inputs i) = Zmod.unsigned (N.v3923 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3923 s i)) at 1.
  unfold R.v3923, N.v3923.
  rewrite ?node_3922.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1700_nr_5F1708.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1700_nr_5F1708 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3924 (s : N.State) (i : N.Inputs) :
  R.v3924 (state s) (inputs i) = Zmod.unsigned (N.v3924 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3924 s i)) at 1.
  unfold R.v3924, N.v3924.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3925 (s : N.State) (i : N.Inputs) :
  R.v3925 (state s) (inputs i) = Zmod.unsigned (N.v3925 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3925 s i)) at 1.
  unfold R.v3925, N.v3925.
  rewrite ?node_3924.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1701_nr_5F1709.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1701_nr_5F1709 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3926 (s : N.State) (i : N.Inputs) :
  R.v3926 (state s) (inputs i) = Zmod.unsigned (N.v3926 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3926 s i)) at 1.
  unfold R.v3926, N.v3926.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3927 (s : N.State) (i : N.Inputs) :
  R.v3927 (state s) (inputs i) = Zmod.unsigned (N.v3927 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3927 s i)) at 1.
  unfold R.v3927, N.v3927.
  rewrite ?node_3926.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1702_nr_5F1710.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1702_nr_5F1710 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3928 (s : N.State) (i : N.Inputs) :
  R.v3928 (state s) (inputs i) = Zmod.unsigned (N.v3928 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3928 s i)) at 1.
  unfold R.v3928, N.v3928.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3929 (s : N.State) (i : N.Inputs) :
  R.v3929 (state s) (inputs i) = Zmod.unsigned (N.v3929 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3929 s i)) at 1.
  unfold R.v3929, N.v3929.
  unfold R.v3021, N.v3021.
  rewrite ?node_3928.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3930 (s : N.State) (i : N.Inputs) :
  R.v3930 (state s) (inputs i) = Zmod.unsigned (N.v3930 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3930 s i)) at 1.
  unfold R.v3930, N.v3930.
  rewrite ?node_3929.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1703_nr_5F1711.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1703_nr_5F1711 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3931 (s : N.State) (i : N.Inputs) :
  R.v3931 (state s) (inputs i) = Zmod.unsigned (N.v3931 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3931 s i)) at 1.
  unfold R.v3931, N.v3931.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3932 (s : N.State) (i : N.Inputs) :
  R.v3932 (state s) (inputs i) = Zmod.unsigned (N.v3932 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3932 s i)) at 1.
  unfold R.v3932, N.v3932.
  rewrite ?node_3931.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1704_nr_5F1712.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1704_nr_5F1712 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3933 (s : N.State) (i : N.Inputs) :
  R.v3933 (state s) (inputs i) = Zmod.unsigned (N.v3933 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3933 s i)) at 1.
  unfold R.v3933, N.v3933.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3934 (s : N.State) (i : N.Inputs) :
  R.v3934 (state s) (inputs i) = Zmod.unsigned (N.v3934 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3934 s i)) at 1.
  unfold R.v3934, N.v3934.
  rewrite ?node_3933.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1705_nr_5F1713.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1705_nr_5F1713 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3935 (s : N.State) (i : N.Inputs) :
  R.v3935 (state s) (inputs i) = Zmod.unsigned (N.v3935 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3935 s i)) at 1.
  unfold R.v3935, N.v3935.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3936 (s : N.State) (i : N.Inputs) :
  R.v3936 (state s) (inputs i) = Zmod.unsigned (N.v3936 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3936 s i)) at 1.
  unfold R.v3936, N.v3936.
  rewrite ?node_3935.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1706_nr_5F1714.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1706_nr_5F1714 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3937 (s : N.State) (i : N.Inputs) :
  R.v3937 (state s) (inputs i) = Zmod.unsigned (N.v3937 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3937 s i)) at 1.
  unfold R.v3937, N.v3937.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3938 (s : N.State) (i : N.Inputs) :
  R.v3938 (state s) (inputs i) = Zmod.unsigned (N.v3938 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3938 s i)) at 1.
  unfold R.v3938, N.v3938.
  rewrite ?node_3937.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1707_nr_5F1715.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1707_nr_5F1715 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3939 (s : N.State) (i : N.Inputs) :
  R.v3939 (state s) (inputs i) = Zmod.unsigned (N.v3939 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3939 s i)) at 1.
  unfold R.v3939, N.v3939.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3940 (s : N.State) (i : N.Inputs) :
  R.v3940 (state s) (inputs i) = Zmod.unsigned (N.v3940 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3940 s i)) at 1.
  unfold R.v3940, N.v3940.
  rewrite ?node_3939.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1708_nr_5F1716.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1708_nr_5F1716 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3941 (s : N.State) (i : N.Inputs) :
  R.v3941 (state s) (inputs i) = Zmod.unsigned (N.v3941 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3941 s i)) at 1.
  unfold R.v3941, N.v3941.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3942 (s : N.State) (i : N.Inputs) :
  R.v3942 (state s) (inputs i) = Zmod.unsigned (N.v3942 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3942 s i)) at 1.
  unfold R.v3942, N.v3942.
  rewrite ?node_3941.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1709_nr_5F1717.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1709_nr_5F1717 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3943 (s : N.State) (i : N.Inputs) :
  R.v3943 (state s) (inputs i) = Zmod.unsigned (N.v3943 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3943 s i)) at 1.
  unfold R.v3943, N.v3943.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3944 (s : N.State) (i : N.Inputs) :
  R.v3944 (state s) (inputs i) = Zmod.unsigned (N.v3944 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3944 s i)) at 1.
  unfold R.v3944, N.v3944.
  rewrite ?node_3943.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1710_nr_5F1718.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1710_nr_5F1718 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3945 (s : N.State) (i : N.Inputs) :
  R.v3945 (state s) (inputs i) = Zmod.unsigned (N.v3945 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3945 s i)) at 1.
  unfold R.v3945, N.v3945.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3946 (s : N.State) (i : N.Inputs) :
  R.v3946 (state s) (inputs i) = Zmod.unsigned (N.v3946 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3946 s i)) at 1.
  unfold R.v3946, N.v3946.
  rewrite ?node_3945.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1711_nr_5F1719.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1711_nr_5F1719 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3947 (s : N.State) (i : N.Inputs) :
  R.v3947 (state s) (inputs i) = Zmod.unsigned (N.v3947 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3947 s i)) at 1.
  unfold R.v3947, N.v3947.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3948 (s : N.State) (i : N.Inputs) :
  R.v3948 (state s) (inputs i) = Zmod.unsigned (N.v3948 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3948 s i)) at 1.
  unfold R.v3948, N.v3948.
  rewrite ?node_3947.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1712_nr_5F1720.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1712_nr_5F1720 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3949 (s : N.State) (i : N.Inputs) :
  R.v3949 (state s) (inputs i) = Zmod.unsigned (N.v3949 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3949 s i)) at 1.
  unfold R.v3949, N.v3949.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3950 (s : N.State) (i : N.Inputs) :
  R.v3950 (state s) (inputs i) = Zmod.unsigned (N.v3950 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3950 s i)) at 1.
  unfold R.v3950, N.v3950.
  rewrite ?node_3949.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1713_nr_5F1721.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1713_nr_5F1721 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3951 (s : N.State) (i : N.Inputs) :
  R.v3951 (state s) (inputs i) = Zmod.unsigned (N.v3951 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3951 s i)) at 1.
  unfold R.v3951, N.v3951.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3952 (s : N.State) (i : N.Inputs) :
  R.v3952 (state s) (inputs i) = Zmod.unsigned (N.v3952 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3952 s i)) at 1.
  unfold R.v3952, N.v3952.
  rewrite ?node_3951.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1714_nr_5F1722.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1714_nr_5F1722 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3953 (s : N.State) (i : N.Inputs) :
  R.v3953 (state s) (inputs i) = Zmod.unsigned (N.v3953 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3953 s i)) at 1.
  unfold R.v3953, N.v3953.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3954 (s : N.State) (i : N.Inputs) :
  R.v3954 (state s) (inputs i) = Zmod.unsigned (N.v3954 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3954 s i)) at 1.
  unfold R.v3954, N.v3954.
  rewrite ?node_3953.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1715_nr_5F1723.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1715_nr_5F1723 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3955 (s : N.State) (i : N.Inputs) :
  R.v3955 (state s) (inputs i) = Zmod.unsigned (N.v3955 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3955 s i)) at 1.
  unfold R.v3955, N.v3955.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3956 (s : N.State) (i : N.Inputs) :
  R.v3956 (state s) (inputs i) = Zmod.unsigned (N.v3956 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3956 s i)) at 1.
  unfold R.v3956, N.v3956.
  rewrite ?node_3955.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1716_nr_5F1724.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1716_nr_5F1724 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3957 (s : N.State) (i : N.Inputs) :
  R.v3957 (state s) (inputs i) = Zmod.unsigned (N.v3957 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3957 s i)) at 1.
  unfold R.v3957, N.v3957.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3958 (s : N.State) (i : N.Inputs) :
  R.v3958 (state s) (inputs i) = Zmod.unsigned (N.v3958 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3958 s i)) at 1.
  unfold R.v3958, N.v3958.
  rewrite ?node_3957.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1717_nr_5F1725.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1717_nr_5F1725 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3959 (s : N.State) (i : N.Inputs) :
  R.v3959 (state s) (inputs i) = Zmod.unsigned (N.v3959 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3959 s i)) at 1.
  unfold R.v3959, N.v3959.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3960 (s : N.State) (i : N.Inputs) :
  R.v3960 (state s) (inputs i) = Zmod.unsigned (N.v3960 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3960 s i)) at 1.
  unfold R.v3960, N.v3960.
  rewrite ?node_3959.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1718_nr_5F1726.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1718_nr_5F1726 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3961 (s : N.State) (i : N.Inputs) :
  R.v3961 (state s) (inputs i) = Zmod.unsigned (N.v3961 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3961 s i)) at 1.
  unfold R.v3961, N.v3961.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3962 (s : N.State) (i : N.Inputs) :
  R.v3962 (state s) (inputs i) = Zmod.unsigned (N.v3962 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3962 s i)) at 1.
  unfold R.v3962, N.v3962.
  rewrite ?node_3961.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1719_nr_5F1727.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1719_nr_5F1727 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3963 (s : N.State) (i : N.Inputs) :
  R.v3963 (state s) (inputs i) = Zmod.unsigned (N.v3963 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3963 s i)) at 1.
  unfold R.v3963, N.v3963.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3964 (s : N.State) (i : N.Inputs) :
  R.v3964 (state s) (inputs i) = Zmod.unsigned (N.v3964 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3964 s i)) at 1.
  unfold R.v3964, N.v3964.
  rewrite ?node_3963.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1720_nr_5F1728.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1720_nr_5F1728 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3965 (s : N.State) (i : N.Inputs) :
  R.v3965 (state s) (inputs i) = Zmod.unsigned (N.v3965 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3965 s i)) at 1.
  unfold R.v3965, N.v3965.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3966 (s : N.State) (i : N.Inputs) :
  R.v3966 (state s) (inputs i) = Zmod.unsigned (N.v3966 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3966 s i)) at 1.
  unfold R.v3966, N.v3966.
  rewrite ?node_3965.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1721_nr_5F1729.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1721_nr_5F1729 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3967 (s : N.State) (i : N.Inputs) :
  R.v3967 (state s) (inputs i) = Zmod.unsigned (N.v3967 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3967 s i)) at 1.
  unfold R.v3967, N.v3967.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3968 (s : N.State) (i : N.Inputs) :
  R.v3968 (state s) (inputs i) = Zmod.unsigned (N.v3968 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3968 s i)) at 1.
  unfold R.v3968, N.v3968.
  rewrite ?node_3967.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1722_nr_5F1730.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1722_nr_5F1730 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3969 (s : N.State) (i : N.Inputs) :
  R.v3969 (state s) (inputs i) = Zmod.unsigned (N.v3969 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3969 s i)) at 1.
  unfold R.v3969, N.v3969.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3970 (s : N.State) (i : N.Inputs) :
  R.v3970 (state s) (inputs i) = Zmod.unsigned (N.v3970 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3970 s i)) at 1.
  unfold R.v3970, N.v3970.
  rewrite ?node_3969.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1723_nr_5F1731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1723_nr_5F1731 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3971 (s : N.State) (i : N.Inputs) :
  R.v3971 (state s) (inputs i) = Zmod.unsigned (N.v3971 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3971 s i)) at 1.
  unfold R.v3971, N.v3971.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3972 (s : N.State) (i : N.Inputs) :
  R.v3972 (state s) (inputs i) = Zmod.unsigned (N.v3972 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3972 s i)) at 1.
  unfold R.v3972, N.v3972.
  rewrite ?node_3971.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1724_nr_5F1732.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1724_nr_5F1732 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3973 (s : N.State) (i : N.Inputs) :
  R.v3973 (state s) (inputs i) = Zmod.unsigned (N.v3973 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3973 s i)) at 1.
  unfold R.v3973, N.v3973.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3974 (s : N.State) (i : N.Inputs) :
  R.v3974 (state s) (inputs i) = Zmod.unsigned (N.v3974 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3974 s i)) at 1.
  unfold R.v3974, N.v3974.
  rewrite ?node_3973.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1725_nr_5F1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1725_nr_5F1733 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3975 (s : N.State) (i : N.Inputs) :
  R.v3975 (state s) (inputs i) = Zmod.unsigned (N.v3975 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3975 s i)) at 1.
  unfold R.v3975, N.v3975.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3976 (s : N.State) (i : N.Inputs) :
  R.v3976 (state s) (inputs i) = Zmod.unsigned (N.v3976 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3976 s i)) at 1.
  unfold R.v3976, N.v3976.
  rewrite ?node_3975.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1726_nr_5F1734.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1726_nr_5F1734 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3977 (s : N.State) (i : N.Inputs) :
  R.v3977 (state s) (inputs i) = Zmod.unsigned (N.v3977 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3977 s i)) at 1.
  unfold R.v3977, N.v3977.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3978 (s : N.State) (i : N.Inputs) :
  R.v3978 (state s) (inputs i) = Zmod.unsigned (N.v3978 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3978 s i)) at 1.
  unfold R.v3978, N.v3978.
  rewrite ?node_3977.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1727_nr_5F1736.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1727_nr_5F1736 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3979 (s : N.State) (i : N.Inputs) :
  R.v3979 (state s) (inputs i) = Zmod.unsigned (N.v3979 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3979 s i)) at 1.
  unfold R.v3979, N.v3979.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3980 (s : N.State) (i : N.Inputs) :
  R.v3980 (state s) (inputs i) = Zmod.unsigned (N.v3980 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3980 s i)) at 1.
  unfold R.v3980, N.v3980.
  rewrite ?node_3979.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1728_nr_5F1737.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1728_nr_5F1737 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3981 (s : N.State) (i : N.Inputs) :
  R.v3981 (state s) (inputs i) = Zmod.unsigned (N.v3981 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3981 s i)) at 1.
  unfold R.v3981, N.v3981.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3982 (s : N.State) (i : N.Inputs) :
  R.v3982 (state s) (inputs i) = Zmod.unsigned (N.v3982 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3982 s i)) at 1.
  unfold R.v3982, N.v3982.
  rewrite ?node_3981.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1729_nr_5F1738.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1729_nr_5F1738 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3983 (s : N.State) (i : N.Inputs) :
  R.v3983 (state s) (inputs i) = Zmod.unsigned (N.v3983 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3983 s i)) at 1.
  unfold R.v3983, N.v3983.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3984 (s : N.State) (i : N.Inputs) :
  R.v3984 (state s) (inputs i) = Zmod.unsigned (N.v3984 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3984 s i)) at 1.
  unfold R.v3984, N.v3984.
  rewrite ?node_3983.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1730_nr_5F1739.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1730_nr_5F1739 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3985 (s : N.State) (i : N.Inputs) :
  R.v3985 (state s) (inputs i) = Zmod.unsigned (N.v3985 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3985 s i)) at 1.
  unfold R.v3985, N.v3985.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3986 (s : N.State) (i : N.Inputs) :
  R.v3986 (state s) (inputs i) = Zmod.unsigned (N.v3986 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3986 s i)) at 1.
  unfold R.v3986, N.v3986.
  rewrite ?node_3985.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1731_nr_5F1740.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1731_nr_5F1740 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3987 (s : N.State) (i : N.Inputs) :
  R.v3987 (state s) (inputs i) = Zmod.unsigned (N.v3987 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3987 s i)) at 1.
  unfold R.v3987, N.v3987.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3988 (s : N.State) (i : N.Inputs) :
  R.v3988 (state s) (inputs i) = Zmod.unsigned (N.v3988 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3988 s i)) at 1.
  unfold R.v3988, N.v3988.
  rewrite ?node_3987.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1732_nr_5F1741.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1732_nr_5F1741 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3989 (s : N.State) (i : N.Inputs) :
  R.v3989 (state s) (inputs i) = Zmod.unsigned (N.v3989 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3989 s i)) at 1.
  unfold R.v3989, N.v3989.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3990 (s : N.State) (i : N.Inputs) :
  R.v3990 (state s) (inputs i) = Zmod.unsigned (N.v3990 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3990 s i)) at 1.
  unfold R.v3990, N.v3990.
  rewrite ?node_3989.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1733_nr_5F1742.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1733_nr_5F1742 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3991 (s : N.State) (i : N.Inputs) :
  R.v3991 (state s) (inputs i) = Zmod.unsigned (N.v3991 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3991 s i)) at 1.
  unfold R.v3991, N.v3991.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3992 (s : N.State) (i : N.Inputs) :
  R.v3992 (state s) (inputs i) = Zmod.unsigned (N.v3992 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3992 s i)) at 1.
  unfold R.v3992, N.v3992.
  rewrite ?node_3991.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1734_nr_5F1743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1734_nr_5F1743 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3993 (s : N.State) (i : N.Inputs) :
  R.v3993 (state s) (inputs i) = Zmod.unsigned (N.v3993 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3993 s i)) at 1.
  unfold R.v3993, N.v3993.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3994 (s : N.State) (i : N.Inputs) :
  R.v3994 (state s) (inputs i) = Zmod.unsigned (N.v3994 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3994 s i)) at 1.
  unfold R.v3994, N.v3994.
  rewrite ?node_3993.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1735_nr_5F1744.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1735_nr_5F1744 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3995 (s : N.State) (i : N.Inputs) :
  R.v3995 (state s) (inputs i) = Zmod.unsigned (N.v3995 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3995 s i)) at 1.
  unfold R.v3995, N.v3995.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3996 (s : N.State) (i : N.Inputs) :
  R.v3996 (state s) (inputs i) = Zmod.unsigned (N.v3996 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3996 s i)) at 1.
  unfold R.v3996, N.v3996.
  rewrite ?node_3995.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1736_nr_5F1745.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1736_nr_5F1745 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3997 (s : N.State) (i : N.Inputs) :
  R.v3997 (state s) (inputs i) = Zmod.unsigned (N.v3997 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3997 s i)) at 1.
  unfold R.v3997, N.v3997.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3998 (s : N.State) (i : N.Inputs) :
  R.v3998 (state s) (inputs i) = Zmod.unsigned (N.v3998 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3998 s i)) at 1.
  unfold R.v3998, N.v3998.
  rewrite ?node_3997.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1737_nr_5F1746.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1737_nr_5F1746 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3999 (s : N.State) (i : N.Inputs) :
  R.v3999 (state s) (inputs i) = Zmod.unsigned (N.v3999 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3999 s i)) at 1.
  unfold R.v3999, N.v3999.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.
