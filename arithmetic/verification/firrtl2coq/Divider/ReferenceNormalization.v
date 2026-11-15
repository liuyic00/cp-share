From Coq Require Import ZArith Lia.
From ArithmeticCommon Require Import BitvectorFacts.
From Divider Require Import Representation LeafWords.
Local Open Scope Z_scope.

Lemma reference_0_normalized s i : normalize 3 (Reference.v0 s i) = Reference.v0 s i.
Proof. unfold Reference.v0, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_0_widen outer s i (larger : (3 <= outer)%nat) : normalize outer (Reference.v0 s i) = Reference.v0 s i.
Proof. rewrite <- (reference_0_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_1_normalized s i : normalize 1 (Reference.v1 s i) = Reference.v1 s i.
Proof. unfold Reference.v1, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_1_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v1 s i) = Reference.v1 s i.
Proof. rewrite <- (reference_1_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_2_normalized s i : normalize 1 (Reference.v2 s i) = Reference.v2 s i.
Proof. unfold Reference.v2, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_2_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v2 s i) = Reference.v2 s i.
Proof. rewrite <- (reference_2_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_3_normalized s i : normalize 3 (Reference.v3 s i) = Reference.v3 s i.
Proof. unfold Reference.v3, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_3_widen outer s i (larger : (3 <= outer)%nat) : normalize outer (Reference.v3 s i) = Reference.v3 s i.
Proof. rewrite <- (reference_3_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_4_normalized s i : normalize 1 (Reference.v4 s i) = Reference.v4 s i.
Proof. unfold Reference.v4, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_4_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v4 s i) = Reference.v4 s i.
Proof. rewrite <- (reference_4_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_5_normalized s i : normalize 3 (Reference.v5 s i) = Reference.v5 s i.
Proof. unfold Reference.v5, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_5_widen outer s i (larger : (3 <= outer)%nat) : normalize outer (Reference.v5 s i) = Reference.v5 s i.
Proof. rewrite <- (reference_5_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_6_normalized s i : normalize 1 (Reference.v6 s i) = Reference.v6 s i.
Proof. unfold Reference.v6, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_6_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v6 s i) = Reference.v6 s i.
Proof. rewrite <- (reference_6_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_7_normalized s i : normalize 3 (Reference.v7 s i) = Reference.v7 s i.
Proof. unfold Reference.v7, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_7_widen outer s i (larger : (3 <= outer)%nat) : normalize outer (Reference.v7 s i) = Reference.v7 s i.
Proof. rewrite <- (reference_7_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_8_normalized s i : normalize 1 (Reference.v8 s i) = Reference.v8 s i.
Proof. unfold Reference.v8, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_8_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v8 s i) = Reference.v8 s i.
Proof. rewrite <- (reference_8_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_9_normalized s i : normalize 6 (Reference.v9 s i) = Reference.v9 s i.
Proof. unfold Reference.v9, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_9_widen outer s i (larger : (6 <= outer)%nat) : normalize outer (Reference.v9 s i) = Reference.v9 s i.
Proof. rewrite <- (reference_9_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_10_normalized s i : normalize 1 (Reference.v10 s i) = Reference.v10 s i.
Proof. unfold Reference.v10, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_10_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v10 s i) = Reference.v10 s i.
Proof. rewrite <- (reference_10_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_11_normalized s i : normalize 3 (Reference.v11 s i) = Reference.v11 s i.
Proof. unfold Reference.v11, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_11_widen outer s i (larger : (3 <= outer)%nat) : normalize outer (Reference.v11 s i) = Reference.v11 s i.
Proof. rewrite <- (reference_11_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_12_normalized s i : normalize 3 (Reference.v12 s i) = Reference.v12 s i.
Proof. unfold Reference.v12, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_12_widen outer s i (larger : (3 <= outer)%nat) : normalize outer (Reference.v12 s i) = Reference.v12 s i.
Proof. rewrite <- (reference_12_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_13_normalized s i : normalize 1 (Reference.v13 s i) = Reference.v13 s i.
Proof. unfold Reference.v13, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_13_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v13 s i) = Reference.v13 s i.
Proof. rewrite <- (reference_13_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_14_normalized s i : normalize 1 (Reference.v14 s i) = Reference.v14 s i.
Proof. unfold Reference.v14, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_14_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v14 s i) = Reference.v14 s i.
Proof. rewrite <- (reference_14_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_15_normalized s i : normalize 3 (Reference.v15 s i) = Reference.v15 s i.
Proof. unfold Reference.v15, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_15_widen outer s i (larger : (3 <= outer)%nat) : normalize outer (Reference.v15 s i) = Reference.v15 s i.
Proof. rewrite <- (reference_15_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_16_normalized s i : normalize 3 (Reference.v16 s i) = Reference.v16 s i.
Proof. unfold Reference.v16, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_16_widen outer s i (larger : (3 <= outer)%nat) : normalize outer (Reference.v16 s i) = Reference.v16 s i.
Proof. rewrite <- (reference_16_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_17_normalized s i : normalize 3 (Reference.v17 s i) = Reference.v17 s i.
Proof. unfold Reference.v17, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_17_widen outer s i (larger : (3 <= outer)%nat) : normalize outer (Reference.v17 s i) = Reference.v17 s i.
Proof. rewrite <- (reference_17_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_18_normalized s i : normalize 3 (Reference.v18 s i) = Reference.v18 s i.
Proof. unfold Reference.v18, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_18_widen outer s i (larger : (3 <= outer)%nat) : normalize outer (Reference.v18 s i) = Reference.v18 s i.
Proof. rewrite <- (reference_18_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_19_normalized s i : normalize 3 (Reference.v19 s i) = Reference.v19 s i.
Proof. unfold Reference.v19, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_19_widen outer s i (larger : (3 <= outer)%nat) : normalize outer (Reference.v19 s i) = Reference.v19 s i.
Proof. rewrite <- (reference_19_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_20_normalized s i : normalize 64 (Reference.v20 s i) = Reference.v20 s i.
Proof. unfold Reference.v20, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_20_widen outer s i (larger : (64 <= outer)%nat) : normalize outer (Reference.v20 s i) = Reference.v20 s i.
Proof. rewrite <- (reference_20_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_21_normalized s i : normalize 1 (Reference.v21 s i) = Reference.v21 s i.
Proof. unfold Reference.v21, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_21_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v21 s i) = Reference.v21 s i.
Proof. rewrite <- (reference_21_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_22_normalized s i : normalize 1 (Reference.v22 s i) = Reference.v22 s i.
Proof. unfold Reference.v22, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_22_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v22 s i) = Reference.v22 s i.
Proof. rewrite <- (reference_22_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_23_normalized s i : normalize 1 (Reference.v23 s i) = Reference.v23 s i.
Proof. unfold Reference.v23, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_23_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v23 s i) = Reference.v23 s i.
Proof. rewrite <- (reference_23_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_24_normalized s i : normalize 1 (Reference.v24 s i) = Reference.v24 s i.
Proof. unfold Reference.v24, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_24_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v24 s i) = Reference.v24 s i.
Proof. rewrite <- (reference_24_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_25_normalized s i : normalize 1 (Reference.v25 s i) = Reference.v25 s i.
Proof. unfold Reference.v25, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_25_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v25 s i) = Reference.v25 s i.
Proof. rewrite <- (reference_25_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_26_normalized s i : normalize 1 (Reference.v26 s i) = Reference.v26 s i.
Proof. unfold Reference.v26, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_26_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v26 s i) = Reference.v26 s i.
Proof. rewrite <- (reference_26_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_27_normalized s i : normalize 63 (Reference.v27 s i) = Reference.v27 s i.
Proof. unfold Reference.v27, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_27_widen outer s i (larger : (63 <= outer)%nat) : normalize outer (Reference.v27 s i) = Reference.v27 s i.
Proof. rewrite <- (reference_27_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_28_normalized s i : normalize 128 (Reference.v28 s i) = Reference.v28 s i.
Proof. unfold Reference.v28, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_28_widen outer s i (larger : (128 <= outer)%nat) : normalize outer (Reference.v28 s i) = Reference.v28 s i.
Proof. rewrite <- (reference_28_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_29_normalized s i : normalize 122 (Reference.v29 s i) = Reference.v29 s i.
Proof. unfold Reference.v29, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_29_widen outer s i (larger : (122 <= outer)%nat) : normalize outer (Reference.v29 s i) = Reference.v29 s i.
Proof. rewrite <- (reference_29_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_30_normalized s i : normalize 128 (Reference.v30 s i) = Reference.v30 s i.
Proof. unfold Reference.v30, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_30_widen outer s i (larger : (128 <= outer)%nat) : normalize outer (Reference.v30 s i) = Reference.v30 s i.
Proof. rewrite <- (reference_30_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_31_normalized s i : normalize 128 (Reference.v31 s i) = Reference.v31 s i.
Proof. unfold Reference.v31, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_31_widen outer s i (larger : (128 <= outer)%nat) : normalize outer (Reference.v31 s i) = Reference.v31 s i.
Proof. rewrite <- (reference_31_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_32_normalized s i : normalize 129 (Reference.v32 s i) = Reference.v32 s i.
Proof. unfold Reference.v32, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_32_widen outer s i (larger : (129 <= outer)%nat) : normalize outer (Reference.v32 s i) = Reference.v32 s i.
Proof. rewrite <- (reference_32_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_33_normalized s i : normalize 65 (Reference.v33 s i) = Reference.v33 s i.
Proof. unfold Reference.v33, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_33_widen outer s i (larger : (65 <= outer)%nat) : normalize outer (Reference.v33 s i) = Reference.v33 s i.
Proof. rewrite <- (reference_33_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_34_normalized s i : normalize 65 (Reference.v34 s i) = Reference.v34 s i.
Proof. unfold Reference.v34, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_34_widen outer s i (larger : (65 <= outer)%nat) : normalize outer (Reference.v34 s i) = Reference.v34 s i.
Proof. rewrite <- (reference_34_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_35_normalized s i : normalize 1 (Reference.v35 s i) = Reference.v35 s i.
Proof. unfold Reference.v35, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_35_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v35 s i) = Reference.v35 s i.
Proof. rewrite <- (reference_35_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_36_normalized s i : normalize 64 (Reference.v36 s i) = Reference.v36 s i.
Proof. unfold Reference.v36, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_36_widen outer s i (larger : (64 <= outer)%nat) : normalize outer (Reference.v36 s i) = Reference.v36 s i.
Proof. rewrite <- (reference_36_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_37_normalized s i : normalize 64 (Reference.v37 s i) = Reference.v37 s i.
Proof. unfold Reference.v37, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_37_widen outer s i (larger : (64 <= outer)%nat) : normalize outer (Reference.v37 s i) = Reference.v37 s i.
Proof. rewrite <- (reference_37_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_38_normalized s i : normalize 64 (Reference.v38 s i) = Reference.v38 s i.
Proof. unfold Reference.v38, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_38_widen outer s i (larger : (64 <= outer)%nat) : normalize outer (Reference.v38 s i) = Reference.v38 s i.
Proof. rewrite <- (reference_38_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_39_normalized s i : normalize 64 (Reference.v39 s i) = Reference.v39 s i.
Proof. unfold Reference.v39, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_39_widen outer s i (larger : (64 <= outer)%nat) : normalize outer (Reference.v39 s i) = Reference.v39 s i.
Proof. rewrite <- (reference_39_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_40_normalized s i : normalize 64 (Reference.v40 s i) = Reference.v40 s i.
Proof. unfold Reference.v40, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_40_widen outer s i (larger : (64 <= outer)%nat) : normalize outer (Reference.v40 s i) = Reference.v40 s i.
Proof. rewrite <- (reference_40_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_41_normalized s i : normalize 129 (Reference.v41 s i) = Reference.v41 s i.
Proof. unfold Reference.v41, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_41_widen outer s i (larger : (129 <= outer)%nat) : normalize outer (Reference.v41 s i) = Reference.v41 s i.
Proof. rewrite <- (reference_41_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_42_normalized s i : normalize 129 (Reference.v42 s i) = Reference.v42 s i.
Proof. unfold Reference.v42, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_42_widen outer s i (larger : (129 <= outer)%nat) : normalize outer (Reference.v42 s i) = Reference.v42 s i.
Proof. rewrite <- (reference_42_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_43_normalized s i : normalize 129 (Reference.v43 s i) = Reference.v43 s i.
Proof. unfold Reference.v43, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_43_widen outer s i (larger : (129 <= outer)%nat) : normalize outer (Reference.v43 s i) = Reference.v43 s i.
Proof. rewrite <- (reference_43_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_44_normalized s i : normalize 129 (Reference.v44 s i) = Reference.v44 s i.
Proof. unfold Reference.v44, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_44_widen outer s i (larger : (129 <= outer)%nat) : normalize outer (Reference.v44 s i) = Reference.v44 s i.
Proof. rewrite <- (reference_44_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_45_normalized s i : normalize 1 (Reference.v45 s i) = Reference.v45 s i.
Proof. unfold Reference.v45, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_45_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v45 s i) = Reference.v45 s i.
Proof. rewrite <- (reference_45_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_46_normalized s i : normalize 1 (Reference.v46 s i) = Reference.v46 s i.
Proof. unfold Reference.v46, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_46_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v46 s i) = Reference.v46 s i.
Proof. rewrite <- (reference_46_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_47_normalized s i : normalize 1 (Reference.v47 s i) = Reference.v47 s i.
Proof. unfold Reference.v47, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_47_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v47 s i) = Reference.v47 s i.
Proof. rewrite <- (reference_47_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_48_normalized s i : normalize 1 (Reference.v48 s i) = Reference.v48 s i.
Proof. unfold Reference.v48, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_48_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v48 s i) = Reference.v48 s i.
Proof. rewrite <- (reference_48_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_49_normalized s i : normalize 1 (Reference.v49 s i) = Reference.v49 s i.
Proof. unfold Reference.v49, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_49_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v49 s i) = Reference.v49 s i.
Proof. rewrite <- (reference_49_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_50_normalized s i : normalize 1 (Reference.v50 s i) = Reference.v50 s i.
Proof. unfold Reference.v50, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_50_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v50 s i) = Reference.v50 s i.
Proof. rewrite <- (reference_50_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_51_normalized s i : normalize 1 (Reference.v51 s i) = Reference.v51 s i.
Proof. unfold Reference.v51, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_51_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v51 s i) = Reference.v51 s i.
Proof. rewrite <- (reference_51_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_52_normalized s i : normalize 1 (Reference.v52 s i) = Reference.v52 s i.
Proof. unfold Reference.v52, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_52_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v52 s i) = Reference.v52 s i.
Proof. rewrite <- (reference_52_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_53_normalized s i : normalize 64 (Reference.v53 s i) = Reference.v53 s i.
Proof. unfold Reference.v53, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_53_widen outer s i (larger : (64 <= outer)%nat) : normalize outer (Reference.v53 s i) = Reference.v53 s i.
Proof. rewrite <- (reference_53_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_54_normalized s i : normalize 64 (Reference.v54 s i) = Reference.v54 s i.
Proof. unfold Reference.v54, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_54_widen outer s i (larger : (64 <= outer)%nat) : normalize outer (Reference.v54 s i) = Reference.v54 s i.
Proof. rewrite <- (reference_54_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_55_normalized s i : normalize 64 (Reference.v55 s i) = Reference.v55 s i.
Proof. unfold Reference.v55, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_55_widen outer s i (larger : (64 <= outer)%nat) : normalize outer (Reference.v55 s i) = Reference.v55 s i.
Proof. rewrite <- (reference_55_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_56_normalized s i : normalize 64 (Reference.v56 s i) = Reference.v56 s i.
Proof. unfold Reference.v56, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_56_widen outer s i (larger : (64 <= outer)%nat) : normalize outer (Reference.v56 s i) = Reference.v56 s i.
Proof. rewrite <- (reference_56_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_57_normalized s i : normalize 64 (Reference.v57 s i) = Reference.v57 s i.
Proof. unfold Reference.v57, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_57_widen outer s i (larger : (64 <= outer)%nat) : normalize outer (Reference.v57 s i) = Reference.v57 s i.
Proof. rewrite <- (reference_57_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_58_normalized s i : normalize 65 (Reference.v58 s i) = Reference.v58 s i.
Proof. unfold Reference.v58, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_58_widen outer s i (larger : (65 <= outer)%nat) : normalize outer (Reference.v58 s i) = Reference.v58 s i.
Proof. rewrite <- (reference_58_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_59_normalized s i : normalize 65 (Reference.v59 s i) = Reference.v59 s i.
Proof. unfold Reference.v59, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_59_widen outer s i (larger : (65 <= outer)%nat) : normalize outer (Reference.v59 s i) = Reference.v59 s i.
Proof. rewrite <- (reference_59_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_60_normalized s i : normalize 1 (Reference.v60 s i) = Reference.v60 s i.
Proof. unfold Reference.v60, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_60_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v60 s i) = Reference.v60 s i.
Proof. rewrite <- (reference_60_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_61_normalized s i : normalize 1 (Reference.v61 s i) = Reference.v61 s i.
Proof. unfold Reference.v61, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_61_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v61 s i) = Reference.v61 s i.
Proof. rewrite <- (reference_61_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_62_normalized s i : normalize 6 (Reference.v62 s i) = Reference.v62 s i.
Proof. unfold Reference.v62, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_62_widen outer s i (larger : (6 <= outer)%nat) : normalize outer (Reference.v62 s i) = Reference.v62 s i.
Proof. rewrite <- (reference_62_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_63_normalized s i : normalize 32 (Reference.v63 s i) = Reference.v63 s i.
Proof. unfold Reference.v63, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_63_widen outer s i (larger : (32 <= outer)%nat) : normalize outer (Reference.v63 s i) = Reference.v63 s i.
Proof. rewrite <- (reference_63_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_64_normalized s i : normalize 32 (Reference.v64 s i) = Reference.v64 s i.
Proof. unfold Reference.v64, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_64_widen outer s i (larger : (32 <= outer)%nat) : normalize outer (Reference.v64 s i) = Reference.v64 s i.
Proof. rewrite <- (reference_64_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_65_normalized s i : normalize 1 (Reference.v65 s i) = Reference.v65 s i.
Proof. unfold Reference.v65, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_65_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v65 s i) = Reference.v65 s i.
Proof. rewrite <- (reference_65_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_66_normalized s i : normalize 16 (Reference.v66 s i) = Reference.v66 s i.
Proof. unfold Reference.v66, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_66_widen outer s i (larger : (16 <= outer)%nat) : normalize outer (Reference.v66 s i) = Reference.v66 s i.
Proof. rewrite <- (reference_66_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_67_normalized s i : normalize 16 (Reference.v67 s i) = Reference.v67 s i.
Proof. unfold Reference.v67, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_67_widen outer s i (larger : (16 <= outer)%nat) : normalize outer (Reference.v67 s i) = Reference.v67 s i.
Proof. rewrite <- (reference_67_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_68_normalized s i : normalize 1 (Reference.v68 s i) = Reference.v68 s i.
Proof. unfold Reference.v68, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_68_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v68 s i) = Reference.v68 s i.
Proof. rewrite <- (reference_68_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_69_normalized s i : normalize 8 (Reference.v69 s i) = Reference.v69 s i.
Proof. unfold Reference.v69, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_69_widen outer s i (larger : (8 <= outer)%nat) : normalize outer (Reference.v69 s i) = Reference.v69 s i.
Proof. rewrite <- (reference_69_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_70_normalized s i : normalize 8 (Reference.v70 s i) = Reference.v70 s i.
Proof. unfold Reference.v70, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_70_widen outer s i (larger : (8 <= outer)%nat) : normalize outer (Reference.v70 s i) = Reference.v70 s i.
Proof. rewrite <- (reference_70_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_71_normalized s i : normalize 1 (Reference.v71 s i) = Reference.v71 s i.
Proof. unfold Reference.v71, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_71_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v71 s i) = Reference.v71 s i.
Proof. rewrite <- (reference_71_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_72_normalized s i : normalize 4 (Reference.v72 s i) = Reference.v72 s i.
Proof. unfold Reference.v72, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_72_widen outer s i (larger : (4 <= outer)%nat) : normalize outer (Reference.v72 s i) = Reference.v72 s i.
Proof. rewrite <- (reference_72_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_73_normalized s i : normalize 4 (Reference.v73 s i) = Reference.v73 s i.
Proof. unfold Reference.v73, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_73_widen outer s i (larger : (4 <= outer)%nat) : normalize outer (Reference.v73 s i) = Reference.v73 s i.
Proof. rewrite <- (reference_73_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_74_normalized s i : normalize 1 (Reference.v74 s i) = Reference.v74 s i.
Proof. unfold Reference.v74, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_74_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v74 s i) = Reference.v74 s i.
Proof. rewrite <- (reference_74_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_75_normalized s i : normalize 1 (Reference.v75 s i) = Reference.v75 s i.
Proof. unfold Reference.v75, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_75_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v75 s i) = Reference.v75 s i.
Proof. rewrite <- (reference_75_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_76_normalized s i : normalize 2 (Reference.v76 s i) = Reference.v76 s i.
Proof. unfold Reference.v76, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_76_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v76 s i) = Reference.v76 s i.
Proof. rewrite <- (reference_76_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_77_normalized s i : normalize 1 (Reference.v77 s i) = Reference.v77 s i.
Proof. unfold Reference.v77, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_77_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v77 s i) = Reference.v77 s i.
Proof. rewrite <- (reference_77_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_78_normalized s i : normalize 2 (Reference.v78 s i) = Reference.v78 s i.
Proof. unfold Reference.v78, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_78_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v78 s i) = Reference.v78 s i.
Proof. rewrite <- (reference_78_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_79_normalized s i : normalize 1 (Reference.v79 s i) = Reference.v79 s i.
Proof. unfold Reference.v79, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_79_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v79 s i) = Reference.v79 s i.
Proof. rewrite <- (reference_79_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_80_normalized s i : normalize 2 (Reference.v80 s i) = Reference.v80 s i.
Proof. unfold Reference.v80, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_80_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v80 s i) = Reference.v80 s i.
Proof. rewrite <- (reference_80_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_81_normalized s i : normalize 2 (Reference.v81 s i) = Reference.v81 s i.
Proof. unfold Reference.v81, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_81_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v81 s i) = Reference.v81 s i.
Proof. rewrite <- (reference_81_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_82_normalized s i : normalize 2 (Reference.v82 s i) = Reference.v82 s i.
Proof. unfold Reference.v82, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_82_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v82 s i) = Reference.v82 s i.
Proof. rewrite <- (reference_82_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_83_normalized s i : normalize 1 (Reference.v83 s i) = Reference.v83 s i.
Proof. unfold Reference.v83, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_83_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v83 s i) = Reference.v83 s i.
Proof. rewrite <- (reference_83_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_84_normalized s i : normalize 1 (Reference.v84 s i) = Reference.v84 s i.
Proof. unfold Reference.v84, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_84_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v84 s i) = Reference.v84 s i.
Proof. rewrite <- (reference_84_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_85_normalized s i : normalize 1 (Reference.v85 s i) = Reference.v85 s i.
Proof. unfold Reference.v85, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_85_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v85 s i) = Reference.v85 s i.
Proof. rewrite <- (reference_85_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_86_normalized s i : normalize 2 (Reference.v86 s i) = Reference.v86 s i.
Proof. unfold Reference.v86, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_86_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v86 s i) = Reference.v86 s i.
Proof. rewrite <- (reference_86_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_87_normalized s i : normalize 2 (Reference.v87 s i) = Reference.v87 s i.
Proof. unfold Reference.v87, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_87_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v87 s i) = Reference.v87 s i.
Proof. rewrite <- (reference_87_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_88_normalized s i : normalize 2 (Reference.v88 s i) = Reference.v88 s i.
Proof. unfold Reference.v88, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_88_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v88 s i) = Reference.v88 s i.
Proof. rewrite <- (reference_88_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_89_normalized s i : normalize 2 (Reference.v89 s i) = Reference.v89 s i.
Proof. unfold Reference.v89, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_89_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v89 s i) = Reference.v89 s i.
Proof. rewrite <- (reference_89_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_90_normalized s i : normalize 3 (Reference.v90 s i) = Reference.v90 s i.
Proof. unfold Reference.v90, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_90_widen outer s i (larger : (3 <= outer)%nat) : normalize outer (Reference.v90 s i) = Reference.v90 s i.
Proof. rewrite <- (reference_90_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_91_normalized s i : normalize 4 (Reference.v91 s i) = Reference.v91 s i.
Proof. unfold Reference.v91, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_91_widen outer s i (larger : (4 <= outer)%nat) : normalize outer (Reference.v91 s i) = Reference.v91 s i.
Proof. rewrite <- (reference_91_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_92_normalized s i : normalize 1 (Reference.v92 s i) = Reference.v92 s i.
Proof. unfold Reference.v92, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_92_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v92 s i) = Reference.v92 s i.
Proof. rewrite <- (reference_92_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_93_normalized s i : normalize 1 (Reference.v93 s i) = Reference.v93 s i.
Proof. unfold Reference.v93, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_93_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v93 s i) = Reference.v93 s i.
Proof. rewrite <- (reference_93_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_94_normalized s i : normalize 1 (Reference.v94 s i) = Reference.v94 s i.
Proof. unfold Reference.v94, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_94_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v94 s i) = Reference.v94 s i.
Proof. rewrite <- (reference_94_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_95_normalized s i : normalize 1 (Reference.v95 s i) = Reference.v95 s i.
Proof. unfold Reference.v95, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_95_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v95 s i) = Reference.v95 s i.
Proof. rewrite <- (reference_95_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_96_normalized s i : normalize 2 (Reference.v96 s i) = Reference.v96 s i.
Proof. unfold Reference.v96, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_96_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v96 s i) = Reference.v96 s i.
Proof. rewrite <- (reference_96_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_97_normalized s i : normalize 2 (Reference.v97 s i) = Reference.v97 s i.
Proof. unfold Reference.v97, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_97_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v97 s i) = Reference.v97 s i.
Proof. rewrite <- (reference_97_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_98_normalized s i : normalize 2 (Reference.v98 s i) = Reference.v98 s i.
Proof. unfold Reference.v98, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_98_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v98 s i) = Reference.v98 s i.
Proof. rewrite <- (reference_98_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_99_normalized s i : normalize 1 (Reference.v99 s i) = Reference.v99 s i.
Proof. unfold Reference.v99, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_99_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v99 s i) = Reference.v99 s i.
Proof. rewrite <- (reference_99_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_100_normalized s i : normalize 1 (Reference.v100 s i) = Reference.v100 s i.
Proof. unfold Reference.v100, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_100_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v100 s i) = Reference.v100 s i.
Proof. rewrite <- (reference_100_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_101_normalized s i : normalize 1 (Reference.v101 s i) = Reference.v101 s i.
Proof. unfold Reference.v101, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_101_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v101 s i) = Reference.v101 s i.
Proof. rewrite <- (reference_101_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_102_normalized s i : normalize 2 (Reference.v102 s i) = Reference.v102 s i.
Proof. unfold Reference.v102, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_102_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v102 s i) = Reference.v102 s i.
Proof. rewrite <- (reference_102_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_103_normalized s i : normalize 2 (Reference.v103 s i) = Reference.v103 s i.
Proof. unfold Reference.v103, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_103_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v103 s i) = Reference.v103 s i.
Proof. rewrite <- (reference_103_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_104_normalized s i : normalize 2 (Reference.v104 s i) = Reference.v104 s i.
Proof. unfold Reference.v104, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_104_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v104 s i) = Reference.v104 s i.
Proof. rewrite <- (reference_104_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_105_normalized s i : normalize 2 (Reference.v105 s i) = Reference.v105 s i.
Proof. unfold Reference.v105, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_105_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v105 s i) = Reference.v105 s i.
Proof. rewrite <- (reference_105_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_106_normalized s i : normalize 3 (Reference.v106 s i) = Reference.v106 s i.
Proof. unfold Reference.v106, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_106_widen outer s i (larger : (3 <= outer)%nat) : normalize outer (Reference.v106 s i) = Reference.v106 s i.
Proof. rewrite <- (reference_106_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_107_normalized s i : normalize 3 (Reference.v107 s i) = Reference.v107 s i.
Proof. unfold Reference.v107, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_107_widen outer s i (larger : (3 <= outer)%nat) : normalize outer (Reference.v107 s i) = Reference.v107 s i.
Proof. rewrite <- (reference_107_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_108_normalized s i : normalize 4 (Reference.v108 s i) = Reference.v108 s i.
Proof. unfold Reference.v108, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_108_widen outer s i (larger : (4 <= outer)%nat) : normalize outer (Reference.v108 s i) = Reference.v108 s i.
Proof. rewrite <- (reference_108_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_109_normalized s i : normalize 8 (Reference.v109 s i) = Reference.v109 s i.
Proof. unfold Reference.v109, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_109_widen outer s i (larger : (8 <= outer)%nat) : normalize outer (Reference.v109 s i) = Reference.v109 s i.
Proof. rewrite <- (reference_109_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_110_normalized s i : normalize 1 (Reference.v110 s i) = Reference.v110 s i.
Proof. unfold Reference.v110, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_110_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v110 s i) = Reference.v110 s i.
Proof. rewrite <- (reference_110_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_111_normalized s i : normalize 4 (Reference.v111 s i) = Reference.v111 s i.
Proof. unfold Reference.v111, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_111_widen outer s i (larger : (4 <= outer)%nat) : normalize outer (Reference.v111 s i) = Reference.v111 s i.
Proof. rewrite <- (reference_111_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_112_normalized s i : normalize 1 (Reference.v112 s i) = Reference.v112 s i.
Proof. unfold Reference.v112, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_112_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v112 s i) = Reference.v112 s i.
Proof. rewrite <- (reference_112_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_113_normalized s i : normalize 1 (Reference.v113 s i) = Reference.v113 s i.
Proof. unfold Reference.v113, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_113_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v113 s i) = Reference.v113 s i.
Proof. rewrite <- (reference_113_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_114_normalized s i : normalize 1 (Reference.v114 s i) = Reference.v114 s i.
Proof. unfold Reference.v114, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_114_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v114 s i) = Reference.v114 s i.
Proof. rewrite <- (reference_114_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_115_normalized s i : normalize 1 (Reference.v115 s i) = Reference.v115 s i.
Proof. unfold Reference.v115, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_115_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v115 s i) = Reference.v115 s i.
Proof. rewrite <- (reference_115_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_116_normalized s i : normalize 2 (Reference.v116 s i) = Reference.v116 s i.
Proof. unfold Reference.v116, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_116_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v116 s i) = Reference.v116 s i.
Proof. rewrite <- (reference_116_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_117_normalized s i : normalize 2 (Reference.v117 s i) = Reference.v117 s i.
Proof. unfold Reference.v117, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_117_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v117 s i) = Reference.v117 s i.
Proof. rewrite <- (reference_117_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_118_normalized s i : normalize 2 (Reference.v118 s i) = Reference.v118 s i.
Proof. unfold Reference.v118, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_118_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v118 s i) = Reference.v118 s i.
Proof. rewrite <- (reference_118_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_119_normalized s i : normalize 1 (Reference.v119 s i) = Reference.v119 s i.
Proof. unfold Reference.v119, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_119_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v119 s i) = Reference.v119 s i.
Proof. rewrite <- (reference_119_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_120_normalized s i : normalize 1 (Reference.v120 s i) = Reference.v120 s i.
Proof. unfold Reference.v120, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_120_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v120 s i) = Reference.v120 s i.
Proof. rewrite <- (reference_120_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_121_normalized s i : normalize 1 (Reference.v121 s i) = Reference.v121 s i.
Proof. unfold Reference.v121, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_121_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v121 s i) = Reference.v121 s i.
Proof. rewrite <- (reference_121_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_122_normalized s i : normalize 2 (Reference.v122 s i) = Reference.v122 s i.
Proof. unfold Reference.v122, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_122_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v122 s i) = Reference.v122 s i.
Proof. rewrite <- (reference_122_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_123_normalized s i : normalize 2 (Reference.v123 s i) = Reference.v123 s i.
Proof. unfold Reference.v123, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_123_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v123 s i) = Reference.v123 s i.
Proof. rewrite <- (reference_123_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_124_normalized s i : normalize 2 (Reference.v124 s i) = Reference.v124 s i.
Proof. unfold Reference.v124, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_124_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v124 s i) = Reference.v124 s i.
Proof. rewrite <- (reference_124_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_125_normalized s i : normalize 2 (Reference.v125 s i) = Reference.v125 s i.
Proof. unfold Reference.v125, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_125_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v125 s i) = Reference.v125 s i.
Proof. rewrite <- (reference_125_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_126_normalized s i : normalize 3 (Reference.v126 s i) = Reference.v126 s i.
Proof. unfold Reference.v126, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_126_widen outer s i (larger : (3 <= outer)%nat) : normalize outer (Reference.v126 s i) = Reference.v126 s i.
Proof. rewrite <- (reference_126_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_127_normalized s i : normalize 4 (Reference.v127 s i) = Reference.v127 s i.
Proof. unfold Reference.v127, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_127_widen outer s i (larger : (4 <= outer)%nat) : normalize outer (Reference.v127 s i) = Reference.v127 s i.
Proof. rewrite <- (reference_127_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_128_normalized s i : normalize 1 (Reference.v128 s i) = Reference.v128 s i.
Proof. unfold Reference.v128, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_128_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v128 s i) = Reference.v128 s i.
Proof. rewrite <- (reference_128_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_129_normalized s i : normalize 1 (Reference.v129 s i) = Reference.v129 s i.
Proof. unfold Reference.v129, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_129_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v129 s i) = Reference.v129 s i.
Proof. rewrite <- (reference_129_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_130_normalized s i : normalize 1 (Reference.v130 s i) = Reference.v130 s i.
Proof. unfold Reference.v130, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_130_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v130 s i) = Reference.v130 s i.
Proof. rewrite <- (reference_130_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_131_normalized s i : normalize 1 (Reference.v131 s i) = Reference.v131 s i.
Proof. unfold Reference.v131, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_131_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v131 s i) = Reference.v131 s i.
Proof. rewrite <- (reference_131_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_132_normalized s i : normalize 2 (Reference.v132 s i) = Reference.v132 s i.
Proof. unfold Reference.v132, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_132_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v132 s i) = Reference.v132 s i.
Proof. rewrite <- (reference_132_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_133_normalized s i : normalize 2 (Reference.v133 s i) = Reference.v133 s i.
Proof. unfold Reference.v133, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_133_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v133 s i) = Reference.v133 s i.
Proof. rewrite <- (reference_133_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_134_normalized s i : normalize 2 (Reference.v134 s i) = Reference.v134 s i.
Proof. unfold Reference.v134, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_134_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v134 s i) = Reference.v134 s i.
Proof. rewrite <- (reference_134_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_135_normalized s i : normalize 1 (Reference.v135 s i) = Reference.v135 s i.
Proof. unfold Reference.v135, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_135_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v135 s i) = Reference.v135 s i.
Proof. rewrite <- (reference_135_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_136_normalized s i : normalize 1 (Reference.v136 s i) = Reference.v136 s i.
Proof. unfold Reference.v136, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_136_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v136 s i) = Reference.v136 s i.
Proof. rewrite <- (reference_136_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_137_normalized s i : normalize 1 (Reference.v137 s i) = Reference.v137 s i.
Proof. unfold Reference.v137, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_137_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v137 s i) = Reference.v137 s i.
Proof. rewrite <- (reference_137_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_138_normalized s i : normalize 2 (Reference.v138 s i) = Reference.v138 s i.
Proof. unfold Reference.v138, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_138_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v138 s i) = Reference.v138 s i.
Proof. rewrite <- (reference_138_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_139_normalized s i : normalize 2 (Reference.v139 s i) = Reference.v139 s i.
Proof. unfold Reference.v139, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_139_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v139 s i) = Reference.v139 s i.
Proof. rewrite <- (reference_139_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_140_normalized s i : normalize 2 (Reference.v140 s i) = Reference.v140 s i.
Proof. unfold Reference.v140, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_140_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v140 s i) = Reference.v140 s i.
Proof. rewrite <- (reference_140_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_141_normalized s i : normalize 2 (Reference.v141 s i) = Reference.v141 s i.
Proof. unfold Reference.v141, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_141_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v141 s i) = Reference.v141 s i.
Proof. rewrite <- (reference_141_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_142_normalized s i : normalize 3 (Reference.v142 s i) = Reference.v142 s i.
Proof. unfold Reference.v142, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_142_widen outer s i (larger : (3 <= outer)%nat) : normalize outer (Reference.v142 s i) = Reference.v142 s i.
Proof. rewrite <- (reference_142_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_143_normalized s i : normalize 3 (Reference.v143 s i) = Reference.v143 s i.
Proof. unfold Reference.v143, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_143_widen outer s i (larger : (3 <= outer)%nat) : normalize outer (Reference.v143 s i) = Reference.v143 s i.
Proof. rewrite <- (reference_143_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_144_normalized s i : normalize 4 (Reference.v144 s i) = Reference.v144 s i.
Proof. unfold Reference.v144, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_144_widen outer s i (larger : (4 <= outer)%nat) : normalize outer (Reference.v144 s i) = Reference.v144 s i.
Proof. rewrite <- (reference_144_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_145_normalized s i : normalize 4 (Reference.v145 s i) = Reference.v145 s i.
Proof. unfold Reference.v145, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_145_widen outer s i (larger : (4 <= outer)%nat) : normalize outer (Reference.v145 s i) = Reference.v145 s i.
Proof. rewrite <- (reference_145_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_146_normalized s i : normalize 5 (Reference.v146 s i) = Reference.v146 s i.
Proof. unfold Reference.v146, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_146_widen outer s i (larger : (5 <= outer)%nat) : normalize outer (Reference.v146 s i) = Reference.v146 s i.
Proof. rewrite <- (reference_146_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_147_normalized s i : normalize 16 (Reference.v147 s i) = Reference.v147 s i.
Proof. unfold Reference.v147, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_147_widen outer s i (larger : (16 <= outer)%nat) : normalize outer (Reference.v147 s i) = Reference.v147 s i.
Proof. rewrite <- (reference_147_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_148_normalized s i : normalize 1 (Reference.v148 s i) = Reference.v148 s i.
Proof. unfold Reference.v148, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_148_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v148 s i) = Reference.v148 s i.
Proof. rewrite <- (reference_148_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_149_normalized s i : normalize 8 (Reference.v149 s i) = Reference.v149 s i.
Proof. unfold Reference.v149, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_149_widen outer s i (larger : (8 <= outer)%nat) : normalize outer (Reference.v149 s i) = Reference.v149 s i.
Proof. rewrite <- (reference_149_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_150_normalized s i : normalize 1 (Reference.v150 s i) = Reference.v150 s i.
Proof. unfold Reference.v150, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_150_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v150 s i) = Reference.v150 s i.
Proof. rewrite <- (reference_150_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_151_normalized s i : normalize 4 (Reference.v151 s i) = Reference.v151 s i.
Proof. unfold Reference.v151, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_151_widen outer s i (larger : (4 <= outer)%nat) : normalize outer (Reference.v151 s i) = Reference.v151 s i.
Proof. rewrite <- (reference_151_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_152_normalized s i : normalize 1 (Reference.v152 s i) = Reference.v152 s i.
Proof. unfold Reference.v152, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_152_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v152 s i) = Reference.v152 s i.
Proof. rewrite <- (reference_152_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_153_normalized s i : normalize 1 (Reference.v153 s i) = Reference.v153 s i.
Proof. unfold Reference.v153, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_153_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v153 s i) = Reference.v153 s i.
Proof. rewrite <- (reference_153_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_154_normalized s i : normalize 1 (Reference.v154 s i) = Reference.v154 s i.
Proof. unfold Reference.v154, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_154_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v154 s i) = Reference.v154 s i.
Proof. rewrite <- (reference_154_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_155_normalized s i : normalize 1 (Reference.v155 s i) = Reference.v155 s i.
Proof. unfold Reference.v155, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_155_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v155 s i) = Reference.v155 s i.
Proof. rewrite <- (reference_155_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_156_normalized s i : normalize 2 (Reference.v156 s i) = Reference.v156 s i.
Proof. unfold Reference.v156, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_156_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v156 s i) = Reference.v156 s i.
Proof. rewrite <- (reference_156_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_157_normalized s i : normalize 2 (Reference.v157 s i) = Reference.v157 s i.
Proof. unfold Reference.v157, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_157_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v157 s i) = Reference.v157 s i.
Proof. rewrite <- (reference_157_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_158_normalized s i : normalize 2 (Reference.v158 s i) = Reference.v158 s i.
Proof. unfold Reference.v158, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_158_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v158 s i) = Reference.v158 s i.
Proof. rewrite <- (reference_158_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_159_normalized s i : normalize 1 (Reference.v159 s i) = Reference.v159 s i.
Proof. unfold Reference.v159, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_159_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v159 s i) = Reference.v159 s i.
Proof. rewrite <- (reference_159_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_160_normalized s i : normalize 1 (Reference.v160 s i) = Reference.v160 s i.
Proof. unfold Reference.v160, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_160_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v160 s i) = Reference.v160 s i.
Proof. rewrite <- (reference_160_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_161_normalized s i : normalize 1 (Reference.v161 s i) = Reference.v161 s i.
Proof. unfold Reference.v161, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_161_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v161 s i) = Reference.v161 s i.
Proof. rewrite <- (reference_161_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_162_normalized s i : normalize 2 (Reference.v162 s i) = Reference.v162 s i.
Proof. unfold Reference.v162, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_162_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v162 s i) = Reference.v162 s i.
Proof. rewrite <- (reference_162_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_163_normalized s i : normalize 2 (Reference.v163 s i) = Reference.v163 s i.
Proof. unfold Reference.v163, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_163_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v163 s i) = Reference.v163 s i.
Proof. rewrite <- (reference_163_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_164_normalized s i : normalize 2 (Reference.v164 s i) = Reference.v164 s i.
Proof. unfold Reference.v164, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_164_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v164 s i) = Reference.v164 s i.
Proof. rewrite <- (reference_164_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_165_normalized s i : normalize 2 (Reference.v165 s i) = Reference.v165 s i.
Proof. unfold Reference.v165, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_165_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v165 s i) = Reference.v165 s i.
Proof. rewrite <- (reference_165_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_166_normalized s i : normalize 3 (Reference.v166 s i) = Reference.v166 s i.
Proof. unfold Reference.v166, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_166_widen outer s i (larger : (3 <= outer)%nat) : normalize outer (Reference.v166 s i) = Reference.v166 s i.
Proof. rewrite <- (reference_166_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_167_normalized s i : normalize 4 (Reference.v167 s i) = Reference.v167 s i.
Proof. unfold Reference.v167, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_167_widen outer s i (larger : (4 <= outer)%nat) : normalize outer (Reference.v167 s i) = Reference.v167 s i.
Proof. rewrite <- (reference_167_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_168_normalized s i : normalize 1 (Reference.v168 s i) = Reference.v168 s i.
Proof. unfold Reference.v168, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_168_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v168 s i) = Reference.v168 s i.
Proof. rewrite <- (reference_168_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_169_normalized s i : normalize 1 (Reference.v169 s i) = Reference.v169 s i.
Proof. unfold Reference.v169, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_169_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v169 s i) = Reference.v169 s i.
Proof. rewrite <- (reference_169_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_170_normalized s i : normalize 1 (Reference.v170 s i) = Reference.v170 s i.
Proof. unfold Reference.v170, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_170_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v170 s i) = Reference.v170 s i.
Proof. rewrite <- (reference_170_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_171_normalized s i : normalize 1 (Reference.v171 s i) = Reference.v171 s i.
Proof. unfold Reference.v171, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_171_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v171 s i) = Reference.v171 s i.
Proof. rewrite <- (reference_171_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_172_normalized s i : normalize 2 (Reference.v172 s i) = Reference.v172 s i.
Proof. unfold Reference.v172, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_172_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v172 s i) = Reference.v172 s i.
Proof. rewrite <- (reference_172_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_173_normalized s i : normalize 2 (Reference.v173 s i) = Reference.v173 s i.
Proof. unfold Reference.v173, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_173_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v173 s i) = Reference.v173 s i.
Proof. rewrite <- (reference_173_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_174_normalized s i : normalize 2 (Reference.v174 s i) = Reference.v174 s i.
Proof. unfold Reference.v174, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_174_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v174 s i) = Reference.v174 s i.
Proof. rewrite <- (reference_174_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_175_normalized s i : normalize 1 (Reference.v175 s i) = Reference.v175 s i.
Proof. unfold Reference.v175, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_175_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v175 s i) = Reference.v175 s i.
Proof. rewrite <- (reference_175_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_176_normalized s i : normalize 1 (Reference.v176 s i) = Reference.v176 s i.
Proof. unfold Reference.v176, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_176_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v176 s i) = Reference.v176 s i.
Proof. rewrite <- (reference_176_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_177_normalized s i : normalize 1 (Reference.v177 s i) = Reference.v177 s i.
Proof. unfold Reference.v177, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_177_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v177 s i) = Reference.v177 s i.
Proof. rewrite <- (reference_177_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_178_normalized s i : normalize 2 (Reference.v178 s i) = Reference.v178 s i.
Proof. unfold Reference.v178, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_178_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v178 s i) = Reference.v178 s i.
Proof. rewrite <- (reference_178_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_179_normalized s i : normalize 2 (Reference.v179 s i) = Reference.v179 s i.
Proof. unfold Reference.v179, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_179_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v179 s i) = Reference.v179 s i.
Proof. rewrite <- (reference_179_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_180_normalized s i : normalize 2 (Reference.v180 s i) = Reference.v180 s i.
Proof. unfold Reference.v180, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_180_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v180 s i) = Reference.v180 s i.
Proof. rewrite <- (reference_180_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_181_normalized s i : normalize 2 (Reference.v181 s i) = Reference.v181 s i.
Proof. unfold Reference.v181, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_181_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v181 s i) = Reference.v181 s i.
Proof. rewrite <- (reference_181_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_182_normalized s i : normalize 3 (Reference.v182 s i) = Reference.v182 s i.
Proof. unfold Reference.v182, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_182_widen outer s i (larger : (3 <= outer)%nat) : normalize outer (Reference.v182 s i) = Reference.v182 s i.
Proof. rewrite <- (reference_182_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_183_normalized s i : normalize 3 (Reference.v183 s i) = Reference.v183 s i.
Proof. unfold Reference.v183, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_183_widen outer s i (larger : (3 <= outer)%nat) : normalize outer (Reference.v183 s i) = Reference.v183 s i.
Proof. rewrite <- (reference_183_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_184_normalized s i : normalize 4 (Reference.v184 s i) = Reference.v184 s i.
Proof. unfold Reference.v184, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_184_widen outer s i (larger : (4 <= outer)%nat) : normalize outer (Reference.v184 s i) = Reference.v184 s i.
Proof. rewrite <- (reference_184_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_185_normalized s i : normalize 8 (Reference.v185 s i) = Reference.v185 s i.
Proof. unfold Reference.v185, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_185_widen outer s i (larger : (8 <= outer)%nat) : normalize outer (Reference.v185 s i) = Reference.v185 s i.
Proof. rewrite <- (reference_185_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_186_normalized s i : normalize 1 (Reference.v186 s i) = Reference.v186 s i.
Proof. unfold Reference.v186, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_186_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v186 s i) = Reference.v186 s i.
Proof. rewrite <- (reference_186_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_187_normalized s i : normalize 4 (Reference.v187 s i) = Reference.v187 s i.
Proof. unfold Reference.v187, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_187_widen outer s i (larger : (4 <= outer)%nat) : normalize outer (Reference.v187 s i) = Reference.v187 s i.
Proof. rewrite <- (reference_187_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_188_normalized s i : normalize 1 (Reference.v188 s i) = Reference.v188 s i.
Proof. unfold Reference.v188, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_188_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v188 s i) = Reference.v188 s i.
Proof. rewrite <- (reference_188_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_189_normalized s i : normalize 1 (Reference.v189 s i) = Reference.v189 s i.
Proof. unfold Reference.v189, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_189_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v189 s i) = Reference.v189 s i.
Proof. rewrite <- (reference_189_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_190_normalized s i : normalize 1 (Reference.v190 s i) = Reference.v190 s i.
Proof. unfold Reference.v190, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_190_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v190 s i) = Reference.v190 s i.
Proof. rewrite <- (reference_190_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_191_normalized s i : normalize 1 (Reference.v191 s i) = Reference.v191 s i.
Proof. unfold Reference.v191, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_191_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v191 s i) = Reference.v191 s i.
Proof. rewrite <- (reference_191_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_192_normalized s i : normalize 2 (Reference.v192 s i) = Reference.v192 s i.
Proof. unfold Reference.v192, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_192_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v192 s i) = Reference.v192 s i.
Proof. rewrite <- (reference_192_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_193_normalized s i : normalize 2 (Reference.v193 s i) = Reference.v193 s i.
Proof. unfold Reference.v193, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_193_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v193 s i) = Reference.v193 s i.
Proof. rewrite <- (reference_193_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_194_normalized s i : normalize 2 (Reference.v194 s i) = Reference.v194 s i.
Proof. unfold Reference.v194, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_194_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v194 s i) = Reference.v194 s i.
Proof. rewrite <- (reference_194_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_195_normalized s i : normalize 1 (Reference.v195 s i) = Reference.v195 s i.
Proof. unfold Reference.v195, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_195_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v195 s i) = Reference.v195 s i.
Proof. rewrite <- (reference_195_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_196_normalized s i : normalize 1 (Reference.v196 s i) = Reference.v196 s i.
Proof. unfold Reference.v196, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_196_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v196 s i) = Reference.v196 s i.
Proof. rewrite <- (reference_196_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_197_normalized s i : normalize 1 (Reference.v197 s i) = Reference.v197 s i.
Proof. unfold Reference.v197, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_197_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v197 s i) = Reference.v197 s i.
Proof. rewrite <- (reference_197_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_198_normalized s i : normalize 2 (Reference.v198 s i) = Reference.v198 s i.
Proof. unfold Reference.v198, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_198_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v198 s i) = Reference.v198 s i.
Proof. rewrite <- (reference_198_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_199_normalized s i : normalize 2 (Reference.v199 s i) = Reference.v199 s i.
Proof. unfold Reference.v199, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_199_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v199 s i) = Reference.v199 s i.
Proof. rewrite <- (reference_199_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_200_normalized s i : normalize 2 (Reference.v200 s i) = Reference.v200 s i.
Proof. unfold Reference.v200, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_200_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v200 s i) = Reference.v200 s i.
Proof. rewrite <- (reference_200_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_201_normalized s i : normalize 2 (Reference.v201 s i) = Reference.v201 s i.
Proof. unfold Reference.v201, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_201_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v201 s i) = Reference.v201 s i.
Proof. rewrite <- (reference_201_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_202_normalized s i : normalize 3 (Reference.v202 s i) = Reference.v202 s i.
Proof. unfold Reference.v202, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_202_widen outer s i (larger : (3 <= outer)%nat) : normalize outer (Reference.v202 s i) = Reference.v202 s i.
Proof. rewrite <- (reference_202_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_203_normalized s i : normalize 4 (Reference.v203 s i) = Reference.v203 s i.
Proof. unfold Reference.v203, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_203_widen outer s i (larger : (4 <= outer)%nat) : normalize outer (Reference.v203 s i) = Reference.v203 s i.
Proof. rewrite <- (reference_203_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_204_normalized s i : normalize 1 (Reference.v204 s i) = Reference.v204 s i.
Proof. unfold Reference.v204, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_204_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v204 s i) = Reference.v204 s i.
Proof. rewrite <- (reference_204_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_205_normalized s i : normalize 1 (Reference.v205 s i) = Reference.v205 s i.
Proof. unfold Reference.v205, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_205_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v205 s i) = Reference.v205 s i.
Proof. rewrite <- (reference_205_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_206_normalized s i : normalize 1 (Reference.v206 s i) = Reference.v206 s i.
Proof. unfold Reference.v206, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_206_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v206 s i) = Reference.v206 s i.
Proof. rewrite <- (reference_206_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_207_normalized s i : normalize 1 (Reference.v207 s i) = Reference.v207 s i.
Proof. unfold Reference.v207, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_207_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v207 s i) = Reference.v207 s i.
Proof. rewrite <- (reference_207_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_208_normalized s i : normalize 2 (Reference.v208 s i) = Reference.v208 s i.
Proof. unfold Reference.v208, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_208_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v208 s i) = Reference.v208 s i.
Proof. rewrite <- (reference_208_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_209_normalized s i : normalize 2 (Reference.v209 s i) = Reference.v209 s i.
Proof. unfold Reference.v209, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_209_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v209 s i) = Reference.v209 s i.
Proof. rewrite <- (reference_209_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_210_normalized s i : normalize 2 (Reference.v210 s i) = Reference.v210 s i.
Proof. unfold Reference.v210, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_210_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v210 s i) = Reference.v210 s i.
Proof. rewrite <- (reference_210_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_211_normalized s i : normalize 1 (Reference.v211 s i) = Reference.v211 s i.
Proof. unfold Reference.v211, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_211_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v211 s i) = Reference.v211 s i.
Proof. rewrite <- (reference_211_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_212_normalized s i : normalize 1 (Reference.v212 s i) = Reference.v212 s i.
Proof. unfold Reference.v212, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_212_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v212 s i) = Reference.v212 s i.
Proof. rewrite <- (reference_212_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_213_normalized s i : normalize 1 (Reference.v213 s i) = Reference.v213 s i.
Proof. unfold Reference.v213, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_213_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v213 s i) = Reference.v213 s i.
Proof. rewrite <- (reference_213_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_214_normalized s i : normalize 2 (Reference.v214 s i) = Reference.v214 s i.
Proof. unfold Reference.v214, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_214_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v214 s i) = Reference.v214 s i.
Proof. rewrite <- (reference_214_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_215_normalized s i : normalize 2 (Reference.v215 s i) = Reference.v215 s i.
Proof. unfold Reference.v215, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_215_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v215 s i) = Reference.v215 s i.
Proof. rewrite <- (reference_215_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_216_normalized s i : normalize 2 (Reference.v216 s i) = Reference.v216 s i.
Proof. unfold Reference.v216, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_216_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v216 s i) = Reference.v216 s i.
Proof. rewrite <- (reference_216_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_217_normalized s i : normalize 2 (Reference.v217 s i) = Reference.v217 s i.
Proof. unfold Reference.v217, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_217_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v217 s i) = Reference.v217 s i.
Proof. rewrite <- (reference_217_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_218_normalized s i : normalize 3 (Reference.v218 s i) = Reference.v218 s i.
Proof. unfold Reference.v218, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_218_widen outer s i (larger : (3 <= outer)%nat) : normalize outer (Reference.v218 s i) = Reference.v218 s i.
Proof. rewrite <- (reference_218_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_219_normalized s i : normalize 3 (Reference.v219 s i) = Reference.v219 s i.
Proof. unfold Reference.v219, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_219_widen outer s i (larger : (3 <= outer)%nat) : normalize outer (Reference.v219 s i) = Reference.v219 s i.
Proof. rewrite <- (reference_219_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_220_normalized s i : normalize 4 (Reference.v220 s i) = Reference.v220 s i.
Proof. unfold Reference.v220, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_220_widen outer s i (larger : (4 <= outer)%nat) : normalize outer (Reference.v220 s i) = Reference.v220 s i.
Proof. rewrite <- (reference_220_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_221_normalized s i : normalize 4 (Reference.v221 s i) = Reference.v221 s i.
Proof. unfold Reference.v221, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_221_widen outer s i (larger : (4 <= outer)%nat) : normalize outer (Reference.v221 s i) = Reference.v221 s i.
Proof. rewrite <- (reference_221_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_222_normalized s i : normalize 5 (Reference.v222 s i) = Reference.v222 s i.
Proof. unfold Reference.v222, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_222_widen outer s i (larger : (5 <= outer)%nat) : normalize outer (Reference.v222 s i) = Reference.v222 s i.
Proof. rewrite <- (reference_222_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_223_normalized s i : normalize 5 (Reference.v223 s i) = Reference.v223 s i.
Proof. unfold Reference.v223, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_223_widen outer s i (larger : (5 <= outer)%nat) : normalize outer (Reference.v223 s i) = Reference.v223 s i.
Proof. rewrite <- (reference_223_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_224_normalized s i : normalize 7 (Reference.v224 s i) = Reference.v224 s i.
Proof. unfold Reference.v224, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_224_widen outer s i (larger : (7 <= outer)%nat) : normalize outer (Reference.v224 s i) = Reference.v224 s i.
Proof. rewrite <- (reference_224_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_225_normalized s i : normalize 7 (Reference.v225 s i) = Reference.v225 s i.
Proof. unfold Reference.v225, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_225_widen outer s i (larger : (7 <= outer)%nat) : normalize outer (Reference.v225 s i) = Reference.v225 s i.
Proof. rewrite <- (reference_225_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_226_normalized s i : normalize 7 (Reference.v226 s i) = Reference.v226 s i.
Proof. unfold Reference.v226, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_226_widen outer s i (larger : (7 <= outer)%nat) : normalize outer (Reference.v226 s i) = Reference.v226 s i.
Proof. rewrite <- (reference_226_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_227_normalized s i : normalize 1 (Reference.v227 s i) = Reference.v227 s i.
Proof. unfold Reference.v227, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_227_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v227 s i) = Reference.v227 s i.
Proof. rewrite <- (reference_227_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_228_normalized s i : normalize 32 (Reference.v228 s i) = Reference.v228 s i.
Proof. unfold Reference.v228, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_228_widen outer s i (larger : (32 <= outer)%nat) : normalize outer (Reference.v228 s i) = Reference.v228 s i.
Proof. rewrite <- (reference_228_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_229_normalized s i : normalize 1 (Reference.v229 s i) = Reference.v229 s i.
Proof. unfold Reference.v229, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_229_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v229 s i) = Reference.v229 s i.
Proof. rewrite <- (reference_229_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_230_normalized s i : normalize 16 (Reference.v230 s i) = Reference.v230 s i.
Proof. unfold Reference.v230, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_230_widen outer s i (larger : (16 <= outer)%nat) : normalize outer (Reference.v230 s i) = Reference.v230 s i.
Proof. rewrite <- (reference_230_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_231_normalized s i : normalize 1 (Reference.v231 s i) = Reference.v231 s i.
Proof. unfold Reference.v231, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_231_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v231 s i) = Reference.v231 s i.
Proof. rewrite <- (reference_231_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_232_normalized s i : normalize 8 (Reference.v232 s i) = Reference.v232 s i.
Proof. unfold Reference.v232, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_232_widen outer s i (larger : (8 <= outer)%nat) : normalize outer (Reference.v232 s i) = Reference.v232 s i.
Proof. rewrite <- (reference_232_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_233_normalized s i : normalize 1 (Reference.v233 s i) = Reference.v233 s i.
Proof. unfold Reference.v233, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_233_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v233 s i) = Reference.v233 s i.
Proof. rewrite <- (reference_233_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_234_normalized s i : normalize 4 (Reference.v234 s i) = Reference.v234 s i.
Proof. unfold Reference.v234, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_234_widen outer s i (larger : (4 <= outer)%nat) : normalize outer (Reference.v234 s i) = Reference.v234 s i.
Proof. rewrite <- (reference_234_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_235_normalized s i : normalize 1 (Reference.v235 s i) = Reference.v235 s i.
Proof. unfold Reference.v235, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_235_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v235 s i) = Reference.v235 s i.
Proof. rewrite <- (reference_235_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_236_normalized s i : normalize 1 (Reference.v236 s i) = Reference.v236 s i.
Proof. unfold Reference.v236, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_236_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v236 s i) = Reference.v236 s i.
Proof. rewrite <- (reference_236_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_237_normalized s i : normalize 1 (Reference.v237 s i) = Reference.v237 s i.
Proof. unfold Reference.v237, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_237_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v237 s i) = Reference.v237 s i.
Proof. rewrite <- (reference_237_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_238_normalized s i : normalize 1 (Reference.v238 s i) = Reference.v238 s i.
Proof. unfold Reference.v238, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_238_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v238 s i) = Reference.v238 s i.
Proof. rewrite <- (reference_238_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_239_normalized s i : normalize 2 (Reference.v239 s i) = Reference.v239 s i.
Proof. unfold Reference.v239, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_239_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v239 s i) = Reference.v239 s i.
Proof. rewrite <- (reference_239_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_240_normalized s i : normalize 2 (Reference.v240 s i) = Reference.v240 s i.
Proof. unfold Reference.v240, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_240_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v240 s i) = Reference.v240 s i.
Proof. rewrite <- (reference_240_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_241_normalized s i : normalize 2 (Reference.v241 s i) = Reference.v241 s i.
Proof. unfold Reference.v241, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_241_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v241 s i) = Reference.v241 s i.
Proof. rewrite <- (reference_241_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_242_normalized s i : normalize 1 (Reference.v242 s i) = Reference.v242 s i.
Proof. unfold Reference.v242, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_242_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v242 s i) = Reference.v242 s i.
Proof. rewrite <- (reference_242_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_243_normalized s i : normalize 1 (Reference.v243 s i) = Reference.v243 s i.
Proof. unfold Reference.v243, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_243_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v243 s i) = Reference.v243 s i.
Proof. rewrite <- (reference_243_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_244_normalized s i : normalize 1 (Reference.v244 s i) = Reference.v244 s i.
Proof. unfold Reference.v244, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_244_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v244 s i) = Reference.v244 s i.
Proof. rewrite <- (reference_244_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_245_normalized s i : normalize 2 (Reference.v245 s i) = Reference.v245 s i.
Proof. unfold Reference.v245, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_245_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v245 s i) = Reference.v245 s i.
Proof. rewrite <- (reference_245_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_246_normalized s i : normalize 2 (Reference.v246 s i) = Reference.v246 s i.
Proof. unfold Reference.v246, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_246_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v246 s i) = Reference.v246 s i.
Proof. rewrite <- (reference_246_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_247_normalized s i : normalize 2 (Reference.v247 s i) = Reference.v247 s i.
Proof. unfold Reference.v247, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_247_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v247 s i) = Reference.v247 s i.
Proof. rewrite <- (reference_247_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_248_normalized s i : normalize 2 (Reference.v248 s i) = Reference.v248 s i.
Proof. unfold Reference.v248, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_248_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v248 s i) = Reference.v248 s i.
Proof. rewrite <- (reference_248_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_249_normalized s i : normalize 3 (Reference.v249 s i) = Reference.v249 s i.
Proof. unfold Reference.v249, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_249_widen outer s i (larger : (3 <= outer)%nat) : normalize outer (Reference.v249 s i) = Reference.v249 s i.
Proof. rewrite <- (reference_249_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_250_normalized s i : normalize 4 (Reference.v250 s i) = Reference.v250 s i.
Proof. unfold Reference.v250, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_250_widen outer s i (larger : (4 <= outer)%nat) : normalize outer (Reference.v250 s i) = Reference.v250 s i.
Proof. rewrite <- (reference_250_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_251_normalized s i : normalize 1 (Reference.v251 s i) = Reference.v251 s i.
Proof. unfold Reference.v251, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_251_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v251 s i) = Reference.v251 s i.
Proof. rewrite <- (reference_251_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_252_normalized s i : normalize 1 (Reference.v252 s i) = Reference.v252 s i.
Proof. unfold Reference.v252, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_252_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v252 s i) = Reference.v252 s i.
Proof. rewrite <- (reference_252_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_253_normalized s i : normalize 1 (Reference.v253 s i) = Reference.v253 s i.
Proof. unfold Reference.v253, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_253_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v253 s i) = Reference.v253 s i.
Proof. rewrite <- (reference_253_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_254_normalized s i : normalize 1 (Reference.v254 s i) = Reference.v254 s i.
Proof. unfold Reference.v254, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_254_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v254 s i) = Reference.v254 s i.
Proof. rewrite <- (reference_254_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_255_normalized s i : normalize 2 (Reference.v255 s i) = Reference.v255 s i.
Proof. unfold Reference.v255, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_255_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v255 s i) = Reference.v255 s i.
Proof. rewrite <- (reference_255_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_256_normalized s i : normalize 2 (Reference.v256 s i) = Reference.v256 s i.
Proof. unfold Reference.v256, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_256_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v256 s i) = Reference.v256 s i.
Proof. rewrite <- (reference_256_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_257_normalized s i : normalize 2 (Reference.v257 s i) = Reference.v257 s i.
Proof. unfold Reference.v257, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_257_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v257 s i) = Reference.v257 s i.
Proof. rewrite <- (reference_257_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_258_normalized s i : normalize 1 (Reference.v258 s i) = Reference.v258 s i.
Proof. unfold Reference.v258, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_258_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v258 s i) = Reference.v258 s i.
Proof. rewrite <- (reference_258_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_259_normalized s i : normalize 1 (Reference.v259 s i) = Reference.v259 s i.
Proof. unfold Reference.v259, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_259_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v259 s i) = Reference.v259 s i.
Proof. rewrite <- (reference_259_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_260_normalized s i : normalize 1 (Reference.v260 s i) = Reference.v260 s i.
Proof. unfold Reference.v260, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_260_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v260 s i) = Reference.v260 s i.
Proof. rewrite <- (reference_260_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_261_normalized s i : normalize 2 (Reference.v261 s i) = Reference.v261 s i.
Proof. unfold Reference.v261, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_261_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v261 s i) = Reference.v261 s i.
Proof. rewrite <- (reference_261_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_262_normalized s i : normalize 2 (Reference.v262 s i) = Reference.v262 s i.
Proof. unfold Reference.v262, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_262_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v262 s i) = Reference.v262 s i.
Proof. rewrite <- (reference_262_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_263_normalized s i : normalize 2 (Reference.v263 s i) = Reference.v263 s i.
Proof. unfold Reference.v263, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_263_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v263 s i) = Reference.v263 s i.
Proof. rewrite <- (reference_263_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_264_normalized s i : normalize 2 (Reference.v264 s i) = Reference.v264 s i.
Proof. unfold Reference.v264, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_264_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v264 s i) = Reference.v264 s i.
Proof. rewrite <- (reference_264_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_265_normalized s i : normalize 3 (Reference.v265 s i) = Reference.v265 s i.
Proof. unfold Reference.v265, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_265_widen outer s i (larger : (3 <= outer)%nat) : normalize outer (Reference.v265 s i) = Reference.v265 s i.
Proof. rewrite <- (reference_265_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_266_normalized s i : normalize 3 (Reference.v266 s i) = Reference.v266 s i.
Proof. unfold Reference.v266, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_266_widen outer s i (larger : (3 <= outer)%nat) : normalize outer (Reference.v266 s i) = Reference.v266 s i.
Proof. rewrite <- (reference_266_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_267_normalized s i : normalize 4 (Reference.v267 s i) = Reference.v267 s i.
Proof. unfold Reference.v267, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_267_widen outer s i (larger : (4 <= outer)%nat) : normalize outer (Reference.v267 s i) = Reference.v267 s i.
Proof. rewrite <- (reference_267_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_268_normalized s i : normalize 8 (Reference.v268 s i) = Reference.v268 s i.
Proof. unfold Reference.v268, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_268_widen outer s i (larger : (8 <= outer)%nat) : normalize outer (Reference.v268 s i) = Reference.v268 s i.
Proof. rewrite <- (reference_268_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_269_normalized s i : normalize 1 (Reference.v269 s i) = Reference.v269 s i.
Proof. unfold Reference.v269, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_269_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v269 s i) = Reference.v269 s i.
Proof. rewrite <- (reference_269_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_270_normalized s i : normalize 4 (Reference.v270 s i) = Reference.v270 s i.
Proof. unfold Reference.v270, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_270_widen outer s i (larger : (4 <= outer)%nat) : normalize outer (Reference.v270 s i) = Reference.v270 s i.
Proof. rewrite <- (reference_270_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_271_normalized s i : normalize 1 (Reference.v271 s i) = Reference.v271 s i.
Proof. unfold Reference.v271, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_271_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v271 s i) = Reference.v271 s i.
Proof. rewrite <- (reference_271_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_272_normalized s i : normalize 1 (Reference.v272 s i) = Reference.v272 s i.
Proof. unfold Reference.v272, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_272_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v272 s i) = Reference.v272 s i.
Proof. rewrite <- (reference_272_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_273_normalized s i : normalize 1 (Reference.v273 s i) = Reference.v273 s i.
Proof. unfold Reference.v273, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_273_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v273 s i) = Reference.v273 s i.
Proof. rewrite <- (reference_273_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_274_normalized s i : normalize 1 (Reference.v274 s i) = Reference.v274 s i.
Proof. unfold Reference.v274, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_274_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v274 s i) = Reference.v274 s i.
Proof. rewrite <- (reference_274_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_275_normalized s i : normalize 2 (Reference.v275 s i) = Reference.v275 s i.
Proof. unfold Reference.v275, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_275_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v275 s i) = Reference.v275 s i.
Proof. rewrite <- (reference_275_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_276_normalized s i : normalize 2 (Reference.v276 s i) = Reference.v276 s i.
Proof. unfold Reference.v276, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_276_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v276 s i) = Reference.v276 s i.
Proof. rewrite <- (reference_276_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_277_normalized s i : normalize 2 (Reference.v277 s i) = Reference.v277 s i.
Proof. unfold Reference.v277, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_277_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v277 s i) = Reference.v277 s i.
Proof. rewrite <- (reference_277_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_278_normalized s i : normalize 1 (Reference.v278 s i) = Reference.v278 s i.
Proof. unfold Reference.v278, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_278_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v278 s i) = Reference.v278 s i.
Proof. rewrite <- (reference_278_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_279_normalized s i : normalize 1 (Reference.v279 s i) = Reference.v279 s i.
Proof. unfold Reference.v279, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_279_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v279 s i) = Reference.v279 s i.
Proof. rewrite <- (reference_279_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_280_normalized s i : normalize 1 (Reference.v280 s i) = Reference.v280 s i.
Proof. unfold Reference.v280, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_280_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v280 s i) = Reference.v280 s i.
Proof. rewrite <- (reference_280_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_281_normalized s i : normalize 2 (Reference.v281 s i) = Reference.v281 s i.
Proof. unfold Reference.v281, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_281_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v281 s i) = Reference.v281 s i.
Proof. rewrite <- (reference_281_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_282_normalized s i : normalize 2 (Reference.v282 s i) = Reference.v282 s i.
Proof. unfold Reference.v282, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_282_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v282 s i) = Reference.v282 s i.
Proof. rewrite <- (reference_282_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_283_normalized s i : normalize 2 (Reference.v283 s i) = Reference.v283 s i.
Proof. unfold Reference.v283, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_283_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v283 s i) = Reference.v283 s i.
Proof. rewrite <- (reference_283_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_284_normalized s i : normalize 2 (Reference.v284 s i) = Reference.v284 s i.
Proof. unfold Reference.v284, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_284_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v284 s i) = Reference.v284 s i.
Proof. rewrite <- (reference_284_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_285_normalized s i : normalize 3 (Reference.v285 s i) = Reference.v285 s i.
Proof. unfold Reference.v285, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_285_widen outer s i (larger : (3 <= outer)%nat) : normalize outer (Reference.v285 s i) = Reference.v285 s i.
Proof. rewrite <- (reference_285_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_286_normalized s i : normalize 4 (Reference.v286 s i) = Reference.v286 s i.
Proof. unfold Reference.v286, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_286_widen outer s i (larger : (4 <= outer)%nat) : normalize outer (Reference.v286 s i) = Reference.v286 s i.
Proof. rewrite <- (reference_286_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_287_normalized s i : normalize 1 (Reference.v287 s i) = Reference.v287 s i.
Proof. unfold Reference.v287, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_287_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v287 s i) = Reference.v287 s i.
Proof. rewrite <- (reference_287_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_288_normalized s i : normalize 1 (Reference.v288 s i) = Reference.v288 s i.
Proof. unfold Reference.v288, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_288_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v288 s i) = Reference.v288 s i.
Proof. rewrite <- (reference_288_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_289_normalized s i : normalize 1 (Reference.v289 s i) = Reference.v289 s i.
Proof. unfold Reference.v289, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_289_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v289 s i) = Reference.v289 s i.
Proof. rewrite <- (reference_289_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_290_normalized s i : normalize 1 (Reference.v290 s i) = Reference.v290 s i.
Proof. unfold Reference.v290, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_290_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v290 s i) = Reference.v290 s i.
Proof. rewrite <- (reference_290_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_291_normalized s i : normalize 2 (Reference.v291 s i) = Reference.v291 s i.
Proof. unfold Reference.v291, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_291_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v291 s i) = Reference.v291 s i.
Proof. rewrite <- (reference_291_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_292_normalized s i : normalize 2 (Reference.v292 s i) = Reference.v292 s i.
Proof. unfold Reference.v292, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_292_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v292 s i) = Reference.v292 s i.
Proof. rewrite <- (reference_292_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_293_normalized s i : normalize 2 (Reference.v293 s i) = Reference.v293 s i.
Proof. unfold Reference.v293, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_293_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v293 s i) = Reference.v293 s i.
Proof. rewrite <- (reference_293_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_294_normalized s i : normalize 1 (Reference.v294 s i) = Reference.v294 s i.
Proof. unfold Reference.v294, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_294_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v294 s i) = Reference.v294 s i.
Proof. rewrite <- (reference_294_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_295_normalized s i : normalize 1 (Reference.v295 s i) = Reference.v295 s i.
Proof. unfold Reference.v295, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_295_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v295 s i) = Reference.v295 s i.
Proof. rewrite <- (reference_295_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_296_normalized s i : normalize 1 (Reference.v296 s i) = Reference.v296 s i.
Proof. unfold Reference.v296, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_296_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v296 s i) = Reference.v296 s i.
Proof. rewrite <- (reference_296_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_297_normalized s i : normalize 2 (Reference.v297 s i) = Reference.v297 s i.
Proof. unfold Reference.v297, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_297_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v297 s i) = Reference.v297 s i.
Proof. rewrite <- (reference_297_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_298_normalized s i : normalize 2 (Reference.v298 s i) = Reference.v298 s i.
Proof. unfold Reference.v298, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_298_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v298 s i) = Reference.v298 s i.
Proof. rewrite <- (reference_298_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_299_normalized s i : normalize 2 (Reference.v299 s i) = Reference.v299 s i.
Proof. unfold Reference.v299, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_299_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v299 s i) = Reference.v299 s i.
Proof. rewrite <- (reference_299_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_300_normalized s i : normalize 2 (Reference.v300 s i) = Reference.v300 s i.
Proof. unfold Reference.v300, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_300_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v300 s i) = Reference.v300 s i.
Proof. rewrite <- (reference_300_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_301_normalized s i : normalize 3 (Reference.v301 s i) = Reference.v301 s i.
Proof. unfold Reference.v301, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_301_widen outer s i (larger : (3 <= outer)%nat) : normalize outer (Reference.v301 s i) = Reference.v301 s i.
Proof. rewrite <- (reference_301_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_302_normalized s i : normalize 3 (Reference.v302 s i) = Reference.v302 s i.
Proof. unfold Reference.v302, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_302_widen outer s i (larger : (3 <= outer)%nat) : normalize outer (Reference.v302 s i) = Reference.v302 s i.
Proof. rewrite <- (reference_302_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_303_normalized s i : normalize 4 (Reference.v303 s i) = Reference.v303 s i.
Proof. unfold Reference.v303, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_303_widen outer s i (larger : (4 <= outer)%nat) : normalize outer (Reference.v303 s i) = Reference.v303 s i.
Proof. rewrite <- (reference_303_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_304_normalized s i : normalize 4 (Reference.v304 s i) = Reference.v304 s i.
Proof. unfold Reference.v304, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_304_widen outer s i (larger : (4 <= outer)%nat) : normalize outer (Reference.v304 s i) = Reference.v304 s i.
Proof. rewrite <- (reference_304_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_305_normalized s i : normalize 5 (Reference.v305 s i) = Reference.v305 s i.
Proof. unfold Reference.v305, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_305_widen outer s i (larger : (5 <= outer)%nat) : normalize outer (Reference.v305 s i) = Reference.v305 s i.
Proof. rewrite <- (reference_305_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_306_normalized s i : normalize 16 (Reference.v306 s i) = Reference.v306 s i.
Proof. unfold Reference.v306, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_306_widen outer s i (larger : (16 <= outer)%nat) : normalize outer (Reference.v306 s i) = Reference.v306 s i.
Proof. rewrite <- (reference_306_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_307_normalized s i : normalize 1 (Reference.v307 s i) = Reference.v307 s i.
Proof. unfold Reference.v307, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_307_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v307 s i) = Reference.v307 s i.
Proof. rewrite <- (reference_307_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_308_normalized s i : normalize 8 (Reference.v308 s i) = Reference.v308 s i.
Proof. unfold Reference.v308, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_308_widen outer s i (larger : (8 <= outer)%nat) : normalize outer (Reference.v308 s i) = Reference.v308 s i.
Proof. rewrite <- (reference_308_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_309_normalized s i : normalize 1 (Reference.v309 s i) = Reference.v309 s i.
Proof. unfold Reference.v309, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_309_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v309 s i) = Reference.v309 s i.
Proof. rewrite <- (reference_309_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_310_normalized s i : normalize 4 (Reference.v310 s i) = Reference.v310 s i.
Proof. unfold Reference.v310, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_310_widen outer s i (larger : (4 <= outer)%nat) : normalize outer (Reference.v310 s i) = Reference.v310 s i.
Proof. rewrite <- (reference_310_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_311_normalized s i : normalize 1 (Reference.v311 s i) = Reference.v311 s i.
Proof. unfold Reference.v311, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_311_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v311 s i) = Reference.v311 s i.
Proof. rewrite <- (reference_311_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_312_normalized s i : normalize 1 (Reference.v312 s i) = Reference.v312 s i.
Proof. unfold Reference.v312, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_312_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v312 s i) = Reference.v312 s i.
Proof. rewrite <- (reference_312_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_313_normalized s i : normalize 1 (Reference.v313 s i) = Reference.v313 s i.
Proof. unfold Reference.v313, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_313_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v313 s i) = Reference.v313 s i.
Proof. rewrite <- (reference_313_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_314_normalized s i : normalize 1 (Reference.v314 s i) = Reference.v314 s i.
Proof. unfold Reference.v314, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_314_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v314 s i) = Reference.v314 s i.
Proof. rewrite <- (reference_314_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_315_normalized s i : normalize 2 (Reference.v315 s i) = Reference.v315 s i.
Proof. unfold Reference.v315, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_315_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v315 s i) = Reference.v315 s i.
Proof. rewrite <- (reference_315_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_316_normalized s i : normalize 2 (Reference.v316 s i) = Reference.v316 s i.
Proof. unfold Reference.v316, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_316_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v316 s i) = Reference.v316 s i.
Proof. rewrite <- (reference_316_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_317_normalized s i : normalize 2 (Reference.v317 s i) = Reference.v317 s i.
Proof. unfold Reference.v317, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_317_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v317 s i) = Reference.v317 s i.
Proof. rewrite <- (reference_317_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_318_normalized s i : normalize 1 (Reference.v318 s i) = Reference.v318 s i.
Proof. unfold Reference.v318, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_318_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v318 s i) = Reference.v318 s i.
Proof. rewrite <- (reference_318_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_319_normalized s i : normalize 1 (Reference.v319 s i) = Reference.v319 s i.
Proof. unfold Reference.v319, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_319_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v319 s i) = Reference.v319 s i.
Proof. rewrite <- (reference_319_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_320_normalized s i : normalize 1 (Reference.v320 s i) = Reference.v320 s i.
Proof. unfold Reference.v320, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_320_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v320 s i) = Reference.v320 s i.
Proof. rewrite <- (reference_320_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_321_normalized s i : normalize 2 (Reference.v321 s i) = Reference.v321 s i.
Proof. unfold Reference.v321, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_321_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v321 s i) = Reference.v321 s i.
Proof. rewrite <- (reference_321_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_322_normalized s i : normalize 2 (Reference.v322 s i) = Reference.v322 s i.
Proof. unfold Reference.v322, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_322_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v322 s i) = Reference.v322 s i.
Proof. rewrite <- (reference_322_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_323_normalized s i : normalize 2 (Reference.v323 s i) = Reference.v323 s i.
Proof. unfold Reference.v323, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_323_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v323 s i) = Reference.v323 s i.
Proof. rewrite <- (reference_323_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_324_normalized s i : normalize 2 (Reference.v324 s i) = Reference.v324 s i.
Proof. unfold Reference.v324, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_324_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v324 s i) = Reference.v324 s i.
Proof. rewrite <- (reference_324_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_325_normalized s i : normalize 3 (Reference.v325 s i) = Reference.v325 s i.
Proof. unfold Reference.v325, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_325_widen outer s i (larger : (3 <= outer)%nat) : normalize outer (Reference.v325 s i) = Reference.v325 s i.
Proof. rewrite <- (reference_325_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_326_normalized s i : normalize 4 (Reference.v326 s i) = Reference.v326 s i.
Proof. unfold Reference.v326, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_326_widen outer s i (larger : (4 <= outer)%nat) : normalize outer (Reference.v326 s i) = Reference.v326 s i.
Proof. rewrite <- (reference_326_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_327_normalized s i : normalize 1 (Reference.v327 s i) = Reference.v327 s i.
Proof. unfold Reference.v327, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_327_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v327 s i) = Reference.v327 s i.
Proof. rewrite <- (reference_327_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_328_normalized s i : normalize 1 (Reference.v328 s i) = Reference.v328 s i.
Proof. unfold Reference.v328, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_328_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v328 s i) = Reference.v328 s i.
Proof. rewrite <- (reference_328_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_329_normalized s i : normalize 1 (Reference.v329 s i) = Reference.v329 s i.
Proof. unfold Reference.v329, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_329_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v329 s i) = Reference.v329 s i.
Proof. rewrite <- (reference_329_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_330_normalized s i : normalize 1 (Reference.v330 s i) = Reference.v330 s i.
Proof. unfold Reference.v330, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_330_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v330 s i) = Reference.v330 s i.
Proof. rewrite <- (reference_330_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_331_normalized s i : normalize 2 (Reference.v331 s i) = Reference.v331 s i.
Proof. unfold Reference.v331, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_331_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v331 s i) = Reference.v331 s i.
Proof. rewrite <- (reference_331_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_332_normalized s i : normalize 2 (Reference.v332 s i) = Reference.v332 s i.
Proof. unfold Reference.v332, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_332_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v332 s i) = Reference.v332 s i.
Proof. rewrite <- (reference_332_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_333_normalized s i : normalize 2 (Reference.v333 s i) = Reference.v333 s i.
Proof. unfold Reference.v333, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_333_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v333 s i) = Reference.v333 s i.
Proof. rewrite <- (reference_333_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_334_normalized s i : normalize 1 (Reference.v334 s i) = Reference.v334 s i.
Proof. unfold Reference.v334, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_334_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v334 s i) = Reference.v334 s i.
Proof. rewrite <- (reference_334_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_335_normalized s i : normalize 1 (Reference.v335 s i) = Reference.v335 s i.
Proof. unfold Reference.v335, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_335_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v335 s i) = Reference.v335 s i.
Proof. rewrite <- (reference_335_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_336_normalized s i : normalize 1 (Reference.v336 s i) = Reference.v336 s i.
Proof. unfold Reference.v336, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_336_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v336 s i) = Reference.v336 s i.
Proof. rewrite <- (reference_336_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_337_normalized s i : normalize 2 (Reference.v337 s i) = Reference.v337 s i.
Proof. unfold Reference.v337, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_337_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v337 s i) = Reference.v337 s i.
Proof. rewrite <- (reference_337_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_338_normalized s i : normalize 2 (Reference.v338 s i) = Reference.v338 s i.
Proof. unfold Reference.v338, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_338_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v338 s i) = Reference.v338 s i.
Proof. rewrite <- (reference_338_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_339_normalized s i : normalize 2 (Reference.v339 s i) = Reference.v339 s i.
Proof. unfold Reference.v339, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_339_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v339 s i) = Reference.v339 s i.
Proof. rewrite <- (reference_339_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_340_normalized s i : normalize 2 (Reference.v340 s i) = Reference.v340 s i.
Proof. unfold Reference.v340, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_340_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v340 s i) = Reference.v340 s i.
Proof. rewrite <- (reference_340_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_341_normalized s i : normalize 3 (Reference.v341 s i) = Reference.v341 s i.
Proof. unfold Reference.v341, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_341_widen outer s i (larger : (3 <= outer)%nat) : normalize outer (Reference.v341 s i) = Reference.v341 s i.
Proof. rewrite <- (reference_341_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_342_normalized s i : normalize 3 (Reference.v342 s i) = Reference.v342 s i.
Proof. unfold Reference.v342, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_342_widen outer s i (larger : (3 <= outer)%nat) : normalize outer (Reference.v342 s i) = Reference.v342 s i.
Proof. rewrite <- (reference_342_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_343_normalized s i : normalize 4 (Reference.v343 s i) = Reference.v343 s i.
Proof. unfold Reference.v343, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_343_widen outer s i (larger : (4 <= outer)%nat) : normalize outer (Reference.v343 s i) = Reference.v343 s i.
Proof. rewrite <- (reference_343_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_344_normalized s i : normalize 8 (Reference.v344 s i) = Reference.v344 s i.
Proof. unfold Reference.v344, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_344_widen outer s i (larger : (8 <= outer)%nat) : normalize outer (Reference.v344 s i) = Reference.v344 s i.
Proof. rewrite <- (reference_344_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_345_normalized s i : normalize 1 (Reference.v345 s i) = Reference.v345 s i.
Proof. unfold Reference.v345, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_345_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v345 s i) = Reference.v345 s i.
Proof. rewrite <- (reference_345_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_346_normalized s i : normalize 4 (Reference.v346 s i) = Reference.v346 s i.
Proof. unfold Reference.v346, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_346_widen outer s i (larger : (4 <= outer)%nat) : normalize outer (Reference.v346 s i) = Reference.v346 s i.
Proof. rewrite <- (reference_346_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_347_normalized s i : normalize 1 (Reference.v347 s i) = Reference.v347 s i.
Proof. unfold Reference.v347, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_347_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v347 s i) = Reference.v347 s i.
Proof. rewrite <- (reference_347_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_348_normalized s i : normalize 1 (Reference.v348 s i) = Reference.v348 s i.
Proof. unfold Reference.v348, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_348_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v348 s i) = Reference.v348 s i.
Proof. rewrite <- (reference_348_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_349_normalized s i : normalize 1 (Reference.v349 s i) = Reference.v349 s i.
Proof. unfold Reference.v349, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_349_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v349 s i) = Reference.v349 s i.
Proof. rewrite <- (reference_349_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_350_normalized s i : normalize 1 (Reference.v350 s i) = Reference.v350 s i.
Proof. unfold Reference.v350, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_350_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v350 s i) = Reference.v350 s i.
Proof. rewrite <- (reference_350_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_351_normalized s i : normalize 2 (Reference.v351 s i) = Reference.v351 s i.
Proof. unfold Reference.v351, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_351_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v351 s i) = Reference.v351 s i.
Proof. rewrite <- (reference_351_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_352_normalized s i : normalize 2 (Reference.v352 s i) = Reference.v352 s i.
Proof. unfold Reference.v352, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_352_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v352 s i) = Reference.v352 s i.
Proof. rewrite <- (reference_352_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_353_normalized s i : normalize 2 (Reference.v353 s i) = Reference.v353 s i.
Proof. unfold Reference.v353, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_353_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v353 s i) = Reference.v353 s i.
Proof. rewrite <- (reference_353_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_354_normalized s i : normalize 1 (Reference.v354 s i) = Reference.v354 s i.
Proof. unfold Reference.v354, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_354_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v354 s i) = Reference.v354 s i.
Proof. rewrite <- (reference_354_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_355_normalized s i : normalize 1 (Reference.v355 s i) = Reference.v355 s i.
Proof. unfold Reference.v355, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_355_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v355 s i) = Reference.v355 s i.
Proof. rewrite <- (reference_355_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_356_normalized s i : normalize 1 (Reference.v356 s i) = Reference.v356 s i.
Proof. unfold Reference.v356, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_356_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v356 s i) = Reference.v356 s i.
Proof. rewrite <- (reference_356_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_357_normalized s i : normalize 2 (Reference.v357 s i) = Reference.v357 s i.
Proof. unfold Reference.v357, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_357_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v357 s i) = Reference.v357 s i.
Proof. rewrite <- (reference_357_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_358_normalized s i : normalize 2 (Reference.v358 s i) = Reference.v358 s i.
Proof. unfold Reference.v358, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_358_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v358 s i) = Reference.v358 s i.
Proof. rewrite <- (reference_358_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_359_normalized s i : normalize 2 (Reference.v359 s i) = Reference.v359 s i.
Proof. unfold Reference.v359, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_359_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v359 s i) = Reference.v359 s i.
Proof. rewrite <- (reference_359_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_360_normalized s i : normalize 2 (Reference.v360 s i) = Reference.v360 s i.
Proof. unfold Reference.v360, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_360_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v360 s i) = Reference.v360 s i.
Proof. rewrite <- (reference_360_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_361_normalized s i : normalize 3 (Reference.v361 s i) = Reference.v361 s i.
Proof. unfold Reference.v361, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_361_widen outer s i (larger : (3 <= outer)%nat) : normalize outer (Reference.v361 s i) = Reference.v361 s i.
Proof. rewrite <- (reference_361_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_362_normalized s i : normalize 4 (Reference.v362 s i) = Reference.v362 s i.
Proof. unfold Reference.v362, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_362_widen outer s i (larger : (4 <= outer)%nat) : normalize outer (Reference.v362 s i) = Reference.v362 s i.
Proof. rewrite <- (reference_362_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_363_normalized s i : normalize 1 (Reference.v363 s i) = Reference.v363 s i.
Proof. unfold Reference.v363, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_363_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v363 s i) = Reference.v363 s i.
Proof. rewrite <- (reference_363_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_364_normalized s i : normalize 1 (Reference.v364 s i) = Reference.v364 s i.
Proof. unfold Reference.v364, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_364_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v364 s i) = Reference.v364 s i.
Proof. rewrite <- (reference_364_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_365_normalized s i : normalize 1 (Reference.v365 s i) = Reference.v365 s i.
Proof. unfold Reference.v365, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_365_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v365 s i) = Reference.v365 s i.
Proof. rewrite <- (reference_365_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_366_normalized s i : normalize 1 (Reference.v366 s i) = Reference.v366 s i.
Proof. unfold Reference.v366, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_366_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v366 s i) = Reference.v366 s i.
Proof. rewrite <- (reference_366_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_367_normalized s i : normalize 2 (Reference.v367 s i) = Reference.v367 s i.
Proof. unfold Reference.v367, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_367_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v367 s i) = Reference.v367 s i.
Proof. rewrite <- (reference_367_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_368_normalized s i : normalize 2 (Reference.v368 s i) = Reference.v368 s i.
Proof. unfold Reference.v368, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_368_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v368 s i) = Reference.v368 s i.
Proof. rewrite <- (reference_368_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_369_normalized s i : normalize 2 (Reference.v369 s i) = Reference.v369 s i.
Proof. unfold Reference.v369, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_369_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v369 s i) = Reference.v369 s i.
Proof. rewrite <- (reference_369_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_370_normalized s i : normalize 1 (Reference.v370 s i) = Reference.v370 s i.
Proof. unfold Reference.v370, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_370_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v370 s i) = Reference.v370 s i.
Proof. rewrite <- (reference_370_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_371_normalized s i : normalize 1 (Reference.v371 s i) = Reference.v371 s i.
Proof. unfold Reference.v371, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_371_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v371 s i) = Reference.v371 s i.
Proof. rewrite <- (reference_371_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_372_normalized s i : normalize 1 (Reference.v372 s i) = Reference.v372 s i.
Proof. unfold Reference.v372, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_372_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v372 s i) = Reference.v372 s i.
Proof. rewrite <- (reference_372_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_373_normalized s i : normalize 2 (Reference.v373 s i) = Reference.v373 s i.
Proof. unfold Reference.v373, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_373_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v373 s i) = Reference.v373 s i.
Proof. rewrite <- (reference_373_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_374_normalized s i : normalize 2 (Reference.v374 s i) = Reference.v374 s i.
Proof. unfold Reference.v374, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_374_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v374 s i) = Reference.v374 s i.
Proof. rewrite <- (reference_374_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_375_normalized s i : normalize 2 (Reference.v375 s i) = Reference.v375 s i.
Proof. unfold Reference.v375, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_375_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v375 s i) = Reference.v375 s i.
Proof. rewrite <- (reference_375_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_376_normalized s i : normalize 2 (Reference.v376 s i) = Reference.v376 s i.
Proof. unfold Reference.v376, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_376_widen outer s i (larger : (2 <= outer)%nat) : normalize outer (Reference.v376 s i) = Reference.v376 s i.
Proof. rewrite <- (reference_376_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_377_normalized s i : normalize 3 (Reference.v377 s i) = Reference.v377 s i.
Proof. unfold Reference.v377, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_377_widen outer s i (larger : (3 <= outer)%nat) : normalize outer (Reference.v377 s i) = Reference.v377 s i.
Proof. rewrite <- (reference_377_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_378_normalized s i : normalize 3 (Reference.v378 s i) = Reference.v378 s i.
Proof. unfold Reference.v378, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_378_widen outer s i (larger : (3 <= outer)%nat) : normalize outer (Reference.v378 s i) = Reference.v378 s i.
Proof. rewrite <- (reference_378_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_379_normalized s i : normalize 4 (Reference.v379 s i) = Reference.v379 s i.
Proof. unfold Reference.v379, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_379_widen outer s i (larger : (4 <= outer)%nat) : normalize outer (Reference.v379 s i) = Reference.v379 s i.
Proof. rewrite <- (reference_379_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_380_normalized s i : normalize 4 (Reference.v380 s i) = Reference.v380 s i.
Proof. unfold Reference.v380, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_380_widen outer s i (larger : (4 <= outer)%nat) : normalize outer (Reference.v380 s i) = Reference.v380 s i.
Proof. rewrite <- (reference_380_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_381_normalized s i : normalize 5 (Reference.v381 s i) = Reference.v381 s i.
Proof. unfold Reference.v381, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_381_widen outer s i (larger : (5 <= outer)%nat) : normalize outer (Reference.v381 s i) = Reference.v381 s i.
Proof. rewrite <- (reference_381_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_382_normalized s i : normalize 5 (Reference.v382 s i) = Reference.v382 s i.
Proof. unfold Reference.v382, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_382_widen outer s i (larger : (5 <= outer)%nat) : normalize outer (Reference.v382 s i) = Reference.v382 s i.
Proof. rewrite <- (reference_382_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_383_normalized s i : normalize 6 (Reference.v383 s i) = Reference.v383 s i.
Proof. unfold Reference.v383, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_383_widen outer s i (larger : (6 <= outer)%nat) : normalize outer (Reference.v383 s i) = Reference.v383 s i.
Proof. rewrite <- (reference_383_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_384_normalized s i : normalize 6 (Reference.v384 s i) = Reference.v384 s i.
Proof. unfold Reference.v384, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_384_widen outer s i (larger : (6 <= outer)%nat) : normalize outer (Reference.v384 s i) = Reference.v384 s i.
Proof. rewrite <- (reference_384_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_385_normalized s i : normalize 7 (Reference.v385 s i) = Reference.v385 s i.
Proof. unfold Reference.v385, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_385_widen outer s i (larger : (7 <= outer)%nat) : normalize outer (Reference.v385 s i) = Reference.v385 s i.
Proof. rewrite <- (reference_385_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_386_normalized s i : normalize 7 (Reference.v386 s i) = Reference.v386 s i.
Proof. unfold Reference.v386, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_386_widen outer s i (larger : (7 <= outer)%nat) : normalize outer (Reference.v386 s i) = Reference.v386 s i.
Proof. rewrite <- (reference_386_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_387_normalized s i : normalize 7 (Reference.v387 s i) = Reference.v387 s i.
Proof. unfold Reference.v387, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_387_widen outer s i (larger : (7 <= outer)%nat) : normalize outer (Reference.v387 s i) = Reference.v387 s i.
Proof. rewrite <- (reference_387_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_388_normalized s i : normalize 1 (Reference.v388 s i) = Reference.v388 s i.
Proof. unfold Reference.v388, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_388_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v388 s i) = Reference.v388 s i.
Proof. rewrite <- (reference_388_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_389_normalized s i : normalize 6 (Reference.v389 s i) = Reference.v389 s i.
Proof. unfold Reference.v389, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_389_widen outer s i (larger : (6 <= outer)%nat) : normalize outer (Reference.v389 s i) = Reference.v389 s i.
Proof. rewrite <- (reference_389_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_390_normalized s i : normalize 6 (Reference.v390 s i) = Reference.v390 s i.
Proof. unfold Reference.v390, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_390_widen outer s i (larger : (6 <= outer)%nat) : normalize outer (Reference.v390 s i) = Reference.v390 s i.
Proof. rewrite <- (reference_390_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_391_normalized s i : normalize 6 (Reference.v391 s i) = Reference.v391 s i.
Proof. unfold Reference.v391, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_391_widen outer s i (larger : (6 <= outer)%nat) : normalize outer (Reference.v391 s i) = Reference.v391 s i.
Proof. rewrite <- (reference_391_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_392_normalized s i : normalize 1 (Reference.v392 s i) = Reference.v392 s i.
Proof. unfold Reference.v392, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_392_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v392 s i) = Reference.v392 s i.
Proof. rewrite <- (reference_392_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_393_normalized s i : normalize 1 (Reference.v393 s i) = Reference.v393 s i.
Proof. unfold Reference.v393, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_393_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v393 s i) = Reference.v393 s i.
Proof. rewrite <- (reference_393_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_394_normalized s i : normalize 6 (Reference.v394 s i) = Reference.v394 s i.
Proof. unfold Reference.v394, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_394_widen outer s i (larger : (6 <= outer)%nat) : normalize outer (Reference.v394 s i) = Reference.v394 s i.
Proof. rewrite <- (reference_394_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_395_normalized s i : normalize 6 (Reference.v395 s i) = Reference.v395 s i.
Proof. unfold Reference.v395, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_395_widen outer s i (larger : (6 <= outer)%nat) : normalize outer (Reference.v395 s i) = Reference.v395 s i.
Proof. rewrite <- (reference_395_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_396_normalized s i : normalize 6 (Reference.v396 s i) = Reference.v396 s i.
Proof. unfold Reference.v396, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_396_widen outer s i (larger : (6 <= outer)%nat) : normalize outer (Reference.v396 s i) = Reference.v396 s i.
Proof. rewrite <- (reference_396_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_397_normalized s i : normalize 6 (Reference.v397 s i) = Reference.v397 s i.
Proof. unfold Reference.v397, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_397_widen outer s i (larger : (6 <= outer)%nat) : normalize outer (Reference.v397 s i) = Reference.v397 s i.
Proof. rewrite <- (reference_397_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_398_normalized s i : normalize 6 (Reference.v398 s i) = Reference.v398 s i.
Proof. unfold Reference.v398, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_398_widen outer s i (larger : (6 <= outer)%nat) : normalize outer (Reference.v398 s i) = Reference.v398 s i.
Proof. rewrite <- (reference_398_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_399_normalized s i : normalize 1 (Reference.v399 s i) = Reference.v399 s i.
Proof. unfold Reference.v399, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_399_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v399 s i) = Reference.v399 s i.
Proof. rewrite <- (reference_399_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_400_normalized s i : normalize 1 (Reference.v400 s i) = Reference.v400 s i.
Proof. unfold Reference.v400, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_400_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v400 s i) = Reference.v400 s i.
Proof. rewrite <- (reference_400_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_401_normalized s i : normalize 1 (Reference.v401 s i) = Reference.v401 s i.
Proof. unfold Reference.v401, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_401_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v401 s i) = Reference.v401 s i.
Proof. rewrite <- (reference_401_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_402_normalized s i : normalize 64 (Reference.v402 s i) = Reference.v402 s i.
Proof. unfold Reference.v402, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_402_widen outer s i (larger : (64 <= outer)%nat) : normalize outer (Reference.v402 s i) = Reference.v402 s i.
Proof. rewrite <- (reference_402_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_403_normalized s i : normalize 64 (Reference.v403 s i) = Reference.v403 s i.
Proof. unfold Reference.v403, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_403_widen outer s i (larger : (64 <= outer)%nat) : normalize outer (Reference.v403 s i) = Reference.v403 s i.
Proof. rewrite <- (reference_403_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_404_normalized s i : normalize 64 (Reference.v404 s i) = Reference.v404 s i.
Proof. unfold Reference.v404, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_404_widen outer s i (larger : (64 <= outer)%nat) : normalize outer (Reference.v404 s i) = Reference.v404 s i.
Proof. rewrite <- (reference_404_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_405_normalized s i : normalize 64 (Reference.v405 s i) = Reference.v405 s i.
Proof. unfold Reference.v405, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_405_widen outer s i (larger : (64 <= outer)%nat) : normalize outer (Reference.v405 s i) = Reference.v405 s i.
Proof. rewrite <- (reference_405_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_406_normalized s i : normalize 64 (Reference.v406 s i) = Reference.v406 s i.
Proof. unfold Reference.v406, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_406_widen outer s i (larger : (64 <= outer)%nat) : normalize outer (Reference.v406 s i) = Reference.v406 s i.
Proof. rewrite <- (reference_406_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_407_normalized s i : normalize 64 (Reference.v407 s i) = Reference.v407 s i.
Proof. unfold Reference.v407, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_407_widen outer s i (larger : (64 <= outer)%nat) : normalize outer (Reference.v407 s i) = Reference.v407 s i.
Proof. rewrite <- (reference_407_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_408_normalized s i : normalize 1 (Reference.v408 s i) = Reference.v408 s i.
Proof. unfold Reference.v408, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_408_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v408 s i) = Reference.v408 s i.
Proof. rewrite <- (reference_408_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_409_normalized s i : normalize 32 (Reference.v409 s i) = Reference.v409 s i.
Proof. unfold Reference.v409, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_409_widen outer s i (larger : (32 <= outer)%nat) : normalize outer (Reference.v409 s i) = Reference.v409 s i.
Proof. rewrite <- (reference_409_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_410_normalized s i : normalize 32 (Reference.v410 s i) = Reference.v410 s i.
Proof. unfold Reference.v410, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_410_widen outer s i (larger : (32 <= outer)%nat) : normalize outer (Reference.v410 s i) = Reference.v410 s i.
Proof. rewrite <- (reference_410_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_411_normalized s i : normalize 64 (Reference.v411 s i) = Reference.v411 s i.
Proof. unfold Reference.v411, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_411_widen outer s i (larger : (64 <= outer)%nat) : normalize outer (Reference.v411 s i) = Reference.v411 s i.
Proof. rewrite <- (reference_411_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_412_normalized s i : normalize 64 (Reference.v412 s i) = Reference.v412 s i.
Proof. unfold Reference.v412, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_412_widen outer s i (larger : (64 <= outer)%nat) : normalize outer (Reference.v412 s i) = Reference.v412 s i.
Proof. rewrite <- (reference_412_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_413_normalized s i : normalize 64 (Reference.v413 s i) = Reference.v413 s i.
Proof. unfold Reference.v413, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_413_widen outer s i (larger : (64 <= outer)%nat) : normalize outer (Reference.v413 s i) = Reference.v413 s i.
Proof. rewrite <- (reference_413_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_414_normalized s i : normalize 1 (Reference.v414 s i) = Reference.v414 s i.
Proof. unfold Reference.v414, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_414_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v414 s i) = Reference.v414 s i.
Proof. rewrite <- (reference_414_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_415_normalized s i : normalize 1 (Reference.v415 s i) = Reference.v415 s i.
Proof. unfold Reference.v415, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_415_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v415 s i) = Reference.v415 s i.
Proof. rewrite <- (reference_415_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_416_normalized s i : normalize 1 (Reference.v416 s i) = Reference.v416 s i.
Proof. unfold Reference.v416, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_416_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v416 s i) = Reference.v416 s i.
Proof. rewrite <- (reference_416_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_417_normalized s i : normalize 64 (Reference.v417 s i) = Reference.v417 s i.
Proof. unfold Reference.v417, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_417_widen outer s i (larger : (64 <= outer)%nat) : normalize outer (Reference.v417 s i) = Reference.v417 s i.
Proof. rewrite <- (reference_417_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_418_normalized s i : normalize 1 (Reference.v418 s i) = Reference.v418 s i.
Proof. unfold Reference.v418, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_418_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v418 s i) = Reference.v418 s i.
Proof. rewrite <- (reference_418_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_419_normalized s i : normalize 1 (Reference.v419 s i) = Reference.v419 s i.
Proof. unfold Reference.v419, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_419_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v419 s i) = Reference.v419 s i.
Proof. rewrite <- (reference_419_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_420_normalized s i : normalize 1 (Reference.v420 s i) = Reference.v420 s i.
Proof. unfold Reference.v420, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_420_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v420 s i) = Reference.v420 s i.
Proof. rewrite <- (reference_420_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_421_normalized s i : normalize 1 (Reference.v421 s i) = Reference.v421 s i.
Proof. unfold Reference.v421, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_421_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v421 s i) = Reference.v421 s i.
Proof. rewrite <- (reference_421_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_422_normalized s i : normalize 128 (Reference.v422 s i) = Reference.v422 s i.
Proof. unfold Reference.v422, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_422_widen outer s i (larger : (128 <= outer)%nat) : normalize outer (Reference.v422 s i) = Reference.v422 s i.
Proof. rewrite <- (reference_422_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_423_normalized s i : normalize 128 (Reference.v423 s i) = Reference.v423 s i.
Proof. unfold Reference.v423, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_423_widen outer s i (larger : (128 <= outer)%nat) : normalize outer (Reference.v423 s i) = Reference.v423 s i.
Proof. rewrite <- (reference_423_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_424_normalized s i : normalize 128 (Reference.v424 s i) = Reference.v424 s i.
Proof. unfold Reference.v424, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_424_widen outer s i (larger : (128 <= outer)%nat) : normalize outer (Reference.v424 s i) = Reference.v424 s i.
Proof. rewrite <- (reference_424_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_425_normalized s i : normalize 129 (Reference.v425 s i) = Reference.v425 s i.
Proof. unfold Reference.v425, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_425_widen outer s i (larger : (129 <= outer)%nat) : normalize outer (Reference.v425 s i) = Reference.v425 s i.
Proof. rewrite <- (reference_425_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_426_normalized s i : normalize 65 (Reference.v426 s i) = Reference.v426 s i.
Proof. unfold Reference.v426, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_426_widen outer s i (larger : (65 <= outer)%nat) : normalize outer (Reference.v426 s i) = Reference.v426 s i.
Proof. rewrite <- (reference_426_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_427_normalized s i : normalize 129 (Reference.v427 s i) = Reference.v427 s i.
Proof. unfold Reference.v427, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_427_widen outer s i (larger : (129 <= outer)%nat) : normalize outer (Reference.v427 s i) = Reference.v427 s i.
Proof. rewrite <- (reference_427_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_428_normalized s i : normalize 129 (Reference.v428 s i) = Reference.v428 s i.
Proof. unfold Reference.v428, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_428_widen outer s i (larger : (129 <= outer)%nat) : normalize outer (Reference.v428 s i) = Reference.v428 s i.
Proof. rewrite <- (reference_428_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_429_normalized s i : normalize 129 (Reference.v429 s i) = Reference.v429 s i.
Proof. unfold Reference.v429, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_429_widen outer s i (larger : (129 <= outer)%nat) : normalize outer (Reference.v429 s i) = Reference.v429 s i.
Proof. rewrite <- (reference_429_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_430_normalized s i : normalize 1 (Reference.v430 s i) = Reference.v430 s i.
Proof. unfold Reference.v430, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_430_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v430 s i) = Reference.v430 s i.
Proof. rewrite <- (reference_430_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_431_normalized s i : normalize 1 (Reference.v431 s i) = Reference.v431 s i.
Proof. unfold Reference.v431, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_431_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v431 s i) = Reference.v431 s i.
Proof. rewrite <- (reference_431_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_432_normalized s i : normalize 1 (Reference.v432 s i) = Reference.v432 s i.
Proof. unfold Reference.v432, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_432_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v432 s i) = Reference.v432 s i.
Proof. rewrite <- (reference_432_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_433_normalized s i : normalize 1 (Reference.v433 s i) = Reference.v433 s i.
Proof. unfold Reference.v433, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_433_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v433 s i) = Reference.v433 s i.
Proof. rewrite <- (reference_433_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_434_normalized s i : normalize 1 (Reference.v434 s i) = Reference.v434 s i.
Proof. unfold Reference.v434, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_434_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v434 s i) = Reference.v434 s i.
Proof. rewrite <- (reference_434_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_435_normalized s i : normalize 1 (Reference.v435 s i) = Reference.v435 s i.
Proof. unfold Reference.v435, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_435_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v435 s i) = Reference.v435 s i.
Proof. rewrite <- (reference_435_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_436_normalized s i : normalize 1 (Reference.v436 s i) = Reference.v436 s i.
Proof. unfold Reference.v436, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_436_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v436 s i) = Reference.v436 s i.
Proof. rewrite <- (reference_436_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_437_normalized s i : normalize 3 (Reference.v437 s i) = Reference.v437 s i.
Proof. unfold Reference.v437, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_437_widen outer s i (larger : (3 <= outer)%nat) : normalize outer (Reference.v437 s i) = Reference.v437 s i.
Proof. rewrite <- (reference_437_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_438_normalized s i : normalize 1 (Reference.v438 s i) = Reference.v438 s i.
Proof. unfold Reference.v438, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_438_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v438 s i) = Reference.v438 s i.
Proof. rewrite <- (reference_438_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_439_normalized s i : normalize 1 (Reference.v439 s i) = Reference.v439 s i.
Proof. unfold Reference.v439, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_439_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v439 s i) = Reference.v439 s i.
Proof. rewrite <- (reference_439_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_440_normalized s i : normalize 1 (Reference.v440 s i) = Reference.v440 s i.
Proof. unfold Reference.v440, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_440_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v440 s i) = Reference.v440 s i.
Proof. rewrite <- (reference_440_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_441_normalized s i : normalize 6 (Reference.v441 s i) = Reference.v441 s i.
Proof. unfold Reference.v441, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_441_widen outer s i (larger : (6 <= outer)%nat) : normalize outer (Reference.v441 s i) = Reference.v441 s i.
Proof. rewrite <- (reference_441_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_442_normalized s i : normalize 6 (Reference.v442 s i) = Reference.v442 s i.
Proof. unfold Reference.v442, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_442_widen outer s i (larger : (6 <= outer)%nat) : normalize outer (Reference.v442 s i) = Reference.v442 s i.
Proof. rewrite <- (reference_442_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_443_normalized s i : normalize 1 (Reference.v443 s i) = Reference.v443 s i.
Proof. unfold Reference.v443, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_443_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v443 s i) = Reference.v443 s i.
Proof. rewrite <- (reference_443_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_444_normalized s i : normalize 1 (Reference.v444 s i) = Reference.v444 s i.
Proof. unfold Reference.v444, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_444_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v444 s i) = Reference.v444 s i.
Proof. rewrite <- (reference_444_normalized s i). apply normalize_widen. exact larger. Qed.
Lemma reference_445_normalized s i : normalize 1 (Reference.v445 s i) = Reference.v445 s i.
Proof. unfold Reference.v445, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.
Lemma reference_445_widen outer s i (larger : (1 <= outer)%nat) : normalize outer (Reference.v445 s i) = Reference.v445 s i.
Proof. rewrite <- (reference_445_normalized s i). apply normalize_widen. exact larger. Qed.
Print Assumptions reference_226_normalized.
