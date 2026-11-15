From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths.
From ArithmeticCommon Require Import BitvectorFacts NormalizationFacts.
From Divider Require Import Stable Representation Typing MuxShapes ScalarOps SliceOps Slices Concats LeafWords ControlStart Controls ReferenceNormalization Commit.
Local Open Scope Z_scope.
Local Opaque Reference.v2 Reference.v4 Reference.v8 Reference.v6 Reference.v31 Reference.v35 Reference.v40.

Lemma data_low_21_reference s i ghost :
 normalize 64 (to_Zpos (word_21 (encoded_leaves s i ghost))) = Reference.v36 s i.
Proof.
 rewrite slice_21_reference. unfold Reference.v33, Reference.v36.
 change (normalize 64 (normalize 65 (Z.shiftr (normalize 129 (Reference.r2_nshiftReg s)) 64)) = normalize 64 (Z.shiftr (normalize 129 (Reference.r2_nshiftReg s)) 64)).
 apply normalize_nested. lia.
Qed.
Lemma data_sub_380_reference s i ghost :
 normalize 64 (to_Zpos (word_380 (encoded_leaves s i ghost))) = Reference.v37 s i.
Proof.
 rewrite slice_integer_380 Z.shiftr_0_r scalar_integer_379 leaf_40_integer.
 rewrite (normalize_nested 64 65); [|lia]. rewrite (normalize_nested 64 66); [|lia].
 change (normalize 64 (to_Zpos (word_21 (encoded_leaves s i ghost)) - normalize 64 (Reference.r5_nbReg s)) =
 normalize 64 (Reference.v36 s i - normalize 64 (Reference.r5_nbReg s))).
 apply normalize_sub_congr; [rewrite data_low_21_reference reference_36_normalized; reflexivity|reflexivity].
Qed.
Local Opaque Reference.v37.
Lemma data_382_reference s i ghost :
 to_Zpos (word_382 (encoded_leaves s i ghost)) = Reference.v39 s i.
Proof.
 rewrite slice_integer_382 Z.shiftr_0_r mux_integer_381 control_378_reference.
 rewrite (normalize_nested 64 65); [|lia].
 unfold Reference.v39.
 change (normalize 64 (if Reference.v35 s i =? 1 then to_Zpos (word_380 (encoded_leaves s i ghost)) else to_Zpos (word_21 (encoded_leaves s i ghost))) =
 normalize 64 (if Reference.v35 s i =? 1 then Reference.v37 s i else Reference.v38 s i)).
 destruct (Reference.v35 s i =? 1).
 - rewrite data_sub_380_reference reference_37_normalized. reflexivity.
 - rewrite data_low_21_reference reference_38_normalized. unfold Reference.v36, Reference.v38. reflexivity.
Qed.
Local Opaque Reference.v39.
Lemma data_384_reference s i ghost :
 to_Zpos (word_384 (encoded_leaves s i ghost)) = Reference.v41 s i.
Proof.
 have Raw := concat_integer_384 s i ghost.
 rewrite concat_integer_383 data_382_reference slice_22_reference control_378_reference in Raw.
 unfold Reference.v41. rewrite !Z.shiftl_mul_pow2; try lia.
 change (to_Zpos (word_384 (encoded_leaves s i ghost)) = normalize 129 ((Reference.v39 s i * modulus 64 + Reference.v40 s i) * modulus 1 + Reference.v35 s i)).
 replace ((Reference.v39 s i * modulus 64 + Reference.v40 s i) * modulus 1 + Reference.v35 s i)
 with (Reference.v35 s i + (Reference.v40 s i + Reference.v39 s i * modulus 64) * modulus 1) by ring.
 rewrite -Raw. symmetry. apply unsigned_normalized. apply encoded_word_384_size.
Qed.
Print Assumptions data_384_reference.

Local Opaque Reference.v41.
Lemma data_393_reference s i ghost :
 to_Zpos (word_393 (encoded_leaves s i ghost)) = Reference.v42 s i.
Proof. rewrite mux_integer_393 control_377_reference data_384_reference leaf_20_integer. reflexivity. Qed.
Lemma data_v32_reference s i : Reference.v32 s i = Reference.v31 s i.
Proof.
 unfold Reference.v32, Reference.v26, Radix2Divider.CIRCTBits.word.
 change (normalize 129 (Reference.v31 s i) = Reference.v31 s i).
 apply reference_31_widen. lia.
Qed.
Local Opaque Reference.v42.
Lemma data_396_reference s i ghost :
 to_Zpos (word_396 (encoded_leaves s i ghost)) = Reference.v43 s i.
Proof.
 rewrite mux_integer_396 control_375_reference control_376_reference data_393_reference.
 unfold Reference.v43. rewrite data_v32_reference. reflexivity.
Qed.
Local Opaque Reference.v43.
Lemma data_404_reference s i ghost :
 to_Zpos (word_404 (encoded_leaves s i ghost)) = Reference.v44 s i.
Proof.
 rewrite mux_integer_404 mux_integer_401 control_16_reference control_52_reference leaf_20_integer data_396_reference.
 unfold Reference.v44, Reference.v25.
 change (normalize 129 (if Reference.v2 s i =? 1 then normalize 129 (Reference.r2_nshiftReg s) else
   normalize 129 (if Reference.v4 s i =? 1 then normalize 129 (Reference.r2_nshiftReg s) else Reference.v43 s i)) =
   normalize 129 (if normalize 1 (Z.lor (Reference.v2 s i) (Reference.v4 s i)) =? 1 then normalize 129 (Reference.r2_nshiftReg s) else Reference.v43 s i)).
 have AB := normalize_range 1 (Reference.v2 s i). rewrite reference_2_normalized in AB.
 have BB := normalize_range 1 (Reference.v4 s i). rewrite reference_4_normalized in BB.
 change (0 <= Reference.v2 s i < 2) in AB. change (0 <= Reference.v4 s i < 2) in BB.
 assert (A : Reference.v2 s i = 0 \/ Reference.v2 s i = 1) by lia.
 assert (B : Reference.v4 s i = 0 \/ Reference.v4 s i = 1) by lia.
 destruct A as [A0 | A1]; destruct B as [B0 | B1];
 rewrite ?A0 ?A1 ?B0 ?B1;
 try change (normalize 1 (Z.lor 0 0)) with 0;
 try change (normalize 1 (Z.lor 0 1)) with 1;
 try change (normalize 1 (Z.lor 1 0)) with 1;
 try change (normalize 1 (Z.lor 1 1)) with 1;
 cbn [Z.eqb]; rewrite ?normalize_nested; try lia; reflexivity.
Qed.

Transparent next_raw_word_20.
Lemma next_raw_data_shape v : next_raw_word_20 v = word_404 v.
Proof.
 unfold next_raw_word_20, next_closed_20, next_expr_20, word_of_eval.
 cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; [reflexivity|reflexivity].
Qed.
Opaque next_raw_word_20.
Local Opaque Reference.v44.
Lemma next_data_reference s i ghost :
 to_Zpos (next_word_20 (encoded_leaves s i ghost)) = Reference.r2_nshiftReg (Reference.step s i).
Proof.
 unfold next_word_20. rewrite unsigned_adapt next_raw_data_shape data_404_reference reference_44_normalized.
 reflexivity.
Qed.
Print Assumptions next_data_reference.
