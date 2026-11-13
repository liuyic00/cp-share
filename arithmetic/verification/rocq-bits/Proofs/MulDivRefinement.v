(* Generated proof certificates, checked by Rocq. *)
From Stdlib Require Import ZArith Lia List Bool Zmod.Bits.
From BitsGenerated Require Import MulDiv.
From ReferenceGenerated Require Import MulDiv.
From BitsProofs Require Import Unsigned BitFacts RefinementTactics.
Module MulDivRefinement.
Module N := BitsGenerated.MulDiv.nMulDiv.
Module R := ReferenceGenerated.MulDiv.nMulDiv.
Module NB := BitsGenerated.MulDiv.CIRCTBits.
Module RB := ReferenceGenerated.MulDiv.CIRCTBits.
Open Scope Z_scope.
Definition inputs (x : N.Inputs) : R.Inputs := R.mkInputs
  (Zmod.unsigned (N.nreset x))
  (Zmod.unsigned (N.nio_5Freq_5Fvalid x))
  (Zmod.unsigned (N.nio_5Freq_5Fbits_5Ffn x))
  (Zmod.unsigned (N.nio_5Freq_5Fbits_5Fdw x))
  (Zmod.unsigned (N.nio_5Freq_5Fbits_5Fin1 x))
  (Zmod.unsigned (N.nio_5Freq_5Fbits_5Fin2 x))
  (Zmod.unsigned (N.nio_5Freq_5Fbits_5Ftag x))
  (Zmod.unsigned (N.nio_5Fkill x))
  (Zmod.unsigned (N.nio_5Fresp_5Fready x)).
Lemma inputs_nreset x : R.nreset (inputs x) = Zmod.unsigned (N.nreset x). Proof. reflexivity. Qed.
Lemma inputs_nio_5Freq_5Fvalid x : R.nio_5Freq_5Fvalid (inputs x) = Zmod.unsigned (N.nio_5Freq_5Fvalid x). Proof. reflexivity. Qed.
Lemma inputs_nio_5Freq_5Fbits_5Ffn x : R.nio_5Freq_5Fbits_5Ffn (inputs x) = Zmod.unsigned (N.nio_5Freq_5Fbits_5Ffn x). Proof. reflexivity. Qed.
Lemma inputs_nio_5Freq_5Fbits_5Fdw x : R.nio_5Freq_5Fbits_5Fdw (inputs x) = Zmod.unsigned (N.nio_5Freq_5Fbits_5Fdw x). Proof. reflexivity. Qed.
Lemma inputs_nio_5Freq_5Fbits_5Fin1 x : R.nio_5Freq_5Fbits_5Fin1 (inputs x) = Zmod.unsigned (N.nio_5Freq_5Fbits_5Fin1 x). Proof. reflexivity. Qed.
Lemma inputs_nio_5Freq_5Fbits_5Fin2 x : R.nio_5Freq_5Fbits_5Fin2 (inputs x) = Zmod.unsigned (N.nio_5Freq_5Fbits_5Fin2 x). Proof. reflexivity. Qed.
Lemma inputs_nio_5Freq_5Fbits_5Ftag x : R.nio_5Freq_5Fbits_5Ftag (inputs x) = Zmod.unsigned (N.nio_5Freq_5Fbits_5Ftag x). Proof. reflexivity. Qed.
Lemma inputs_nio_5Fkill x : R.nio_5Fkill (inputs x) = Zmod.unsigned (N.nio_5Fkill x). Proof. reflexivity. Qed.
Lemma inputs_nio_5Fresp_5Fready x : R.nio_5Fresp_5Fready (inputs x) = Zmod.unsigned (N.nio_5Fresp_5Fready x). Proof. reflexivity. Qed.
Definition state (x : N.State) : R.State := R.mkState
  (Zmod.unsigned (N.r0_nstate x))
  (Zmod.unsigned (N.r1_nreq_5Fdw x))
  (Zmod.unsigned (N.r2_nreq_5Ftag x))
  (Zmod.unsigned (N.r3_ncount x))
  (Zmod.unsigned (N.r4_nneg_5Fout x))
  (Zmod.unsigned (N.r5_nisHi x))
  (Zmod.unsigned (N.r6_nresHi x))
  (Zmod.unsigned (N.r7_ndivisor x))
  (Zmod.unsigned (N.r8_nremainder x)).
Lemma state_r0_nstate x : R.r0_nstate (state x) = Zmod.unsigned (N.r0_nstate x). Proof. reflexivity. Qed.
Lemma state_r1_nreq_5Fdw x : R.r1_nreq_5Fdw (state x) = Zmod.unsigned (N.r1_nreq_5Fdw x). Proof. reflexivity. Qed.
Lemma state_r2_nreq_5Ftag x : R.r2_nreq_5Ftag (state x) = Zmod.unsigned (N.r2_nreq_5Ftag x). Proof. reflexivity. Qed.
Lemma state_r3_ncount x : R.r3_ncount (state x) = Zmod.unsigned (N.r3_ncount x). Proof. reflexivity. Qed.
Lemma state_r4_nneg_5Fout x : R.r4_nneg_5Fout (state x) = Zmod.unsigned (N.r4_nneg_5Fout x). Proof. reflexivity. Qed.
Lemma state_r5_nisHi x : R.r5_nisHi (state x) = Zmod.unsigned (N.r5_nisHi x). Proof. reflexivity. Qed.
Lemma state_r6_nresHi x : R.r6_nresHi (state x) = Zmod.unsigned (N.r6_nresHi x). Proof. reflexivity. Qed.
Lemma state_r7_ndivisor x : R.r7_ndivisor (state x) = Zmod.unsigned (N.r7_ndivisor x). Proof. reflexivity. Qed.
Lemma state_r8_nremainder x : R.r8_nremainder (state x) = Zmod.unsigned (N.r8_nremainder x). Proof. reflexivity. Qed.
Definition outputs (x : N.Outputs) : R.Outputs := R.mkOutputs
  (Zmod.unsigned (N.nio_5Freq_5Fready x))
  (Zmod.unsigned (N.nio_5Fresp_5Fvalid x))
  (Zmod.unsigned (N.nio_5Fresp_5Fbits_5Fdata x))
  (Zmod.unsigned (N.nio_5Fresp_5Fbits_5Ftag x)).
Lemma outputs_nio_5Freq_5Fready x : R.nio_5Freq_5Fready (outputs x) = Zmod.unsigned (N.nio_5Freq_5Fready x). Proof. reflexivity. Qed.
Lemma outputs_nio_5Fresp_5Fvalid x : R.nio_5Fresp_5Fvalid (outputs x) = Zmod.unsigned (N.nio_5Fresp_5Fvalid x). Proof. reflexivity. Qed.
Lemma outputs_nio_5Fresp_5Fbits_5Fdata x : R.nio_5Fresp_5Fbits_5Fdata (outputs x) = Zmod.unsigned (N.nio_5Fresp_5Fbits_5Fdata x). Proof. reflexivity. Qed.
Lemma outputs_nio_5Fresp_5Fbits_5Ftag x : R.nio_5Fresp_5Fbits_5Ftag (outputs x) = Zmod.unsigned (N.nio_5Fresp_5Fbits_5Ftag x). Proof. reflexivity. Qed.
Lemma repeat_32 (x : bits 1) : RB.repeatWord 32 1 (Zmod.unsigned x) mod 2^32 = Zmod.unsigned (NB.repeatBits 32 32 x).
Proof. destruct (BitFacts.bit_cases x) as [h|h]; rewrite h; vm_compute; reflexivity. Qed.
Lemma repeat_65 (x : bits 1) : RB.repeatWord 65 1 (Zmod.unsigned x) mod 2^65 = Zmod.unsigned (NB.repeatBits 65 65 x).
Proof. destruct (BitFacts.bit_cases x) as [h|h]; rewrite h; vm_compute; reflexivity. Qed.
Ltac finish_numeric :=
  repeat first [rewrite Zmod.unsigned_sub | rewrite Zmod.unsigned_slu];
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Lemma node_0 (s : N.State) (i : N.Inputs) : R.v0 (state s) (inputs i) = Zmod.unsigned (N.v0 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v0 s i)) at 1; unfold R.v0, N.v0.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_1 (s : N.State) (i : N.Inputs) : R.v1 (state s) (inputs i) = Zmod.unsigned (N.v1 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v1 s i)) at 1; unfold R.v1, N.v1.
  unfold R.v0, N.v0.
  rewrite !state_r0_nstate.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r0_nstate s)).
  finish_numeric.
Qed.
Lemma node_2 (s : N.State) (i : N.Inputs) : R.v2 (state s) (inputs i) = Zmod.unsigned (N.v2 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v2 s i)) at 1; unfold R.v2, N.v2.
  rewrite ?node_1.
  rewrite !inputs_nio_5Freq_5Fvalid.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Freq_5Fvalid i)).
  finish_numeric.
Qed.
Lemma node_3 (s : N.State) (i : N.Inputs) : R.v3 (state s) (inputs i) = Zmod.unsigned (N.v3 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v3 s i)) at 1; unfold R.v3, N.v3.
  rewrite !inputs_nio_5Freq_5Fbits_5Ffn.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Freq_5Fbits_5Ffn i)).
  finish_numeric.
Qed.
Lemma node_4 (s : N.State) (i : N.Inputs) : R.v4 (state s) (inputs i) = Zmod.unsigned (N.v4 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v4 s i)) at 1; unfold R.v4, N.v4.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_5 (s : N.State) (i : N.Inputs) : R.v5 (state s) (inputs i) = Zmod.unsigned (N.v5 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v5 s i)) at 1; unfold R.v5, N.v5.
  rewrite ?node_3.
  unfold R.v4, N.v4.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_6 (s : N.State) (i : N.Inputs) : R.v6 (state s) (inputs i) = Zmod.unsigned (N.v6 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v6 s i)) at 1; unfold R.v6, N.v6.
  rewrite ?node_5.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_7 (s : N.State) (i : N.Inputs) : R.v7 (state s) (inputs i) = Zmod.unsigned (N.v7 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v7 s i)) at 1; unfold R.v7, N.v7.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_8 (s : N.State) (i : N.Inputs) : R.v8 (state s) (inputs i) = Zmod.unsigned (N.v8 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v8 s i)) at 1; unfold R.v8, N.v8.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_9 (s : N.State) (i : N.Inputs) : R.v9 (state s) (inputs i) = Zmod.unsigned (N.v9 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v9 s i)) at 1; unfold R.v9, N.v9.
  rewrite ?node_5.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_10 (s : N.State) (i : N.Inputs) : R.v10 (state s) (inputs i) = Zmod.unsigned (N.v10 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v10 s i)) at 1; unfold R.v10, N.v10.
  rewrite ?node_5.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_11 (s : N.State) (i : N.Inputs) : R.v11 (state s) (inputs i) = Zmod.unsigned (N.v11 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v11 s i)) at 1; unfold R.v11, N.v11.
  rewrite ?node_6.
  rewrite ?node_10.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_12 (s : N.State) (i : N.Inputs) : R.v12 (state s) (inputs i) = Zmod.unsigned (N.v12 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v12 s i)) at 1; unfold R.v12, N.v12.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_13 (s : N.State) (i : N.Inputs) : R.v13 (state s) (inputs i) = Zmod.unsigned (N.v13 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v13 s i)) at 1; unfold R.v13, N.v13.
  rewrite ?node_11.
  unfold R.v12, N.v12.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_14 (s : N.State) (i : N.Inputs) : R.v14 (state s) (inputs i) = Zmod.unsigned (N.v14 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v14 s i)) at 1; unfold R.v14, N.v14.
  rewrite ?node_9.
  rewrite ?node_13.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_15 (s : N.State) (i : N.Inputs) : R.v15 (state s) (inputs i) = Zmod.unsigned (N.v15 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v15 s i)) at 1; unfold R.v15, N.v15.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_16 (s : N.State) (i : N.Inputs) : R.v16 (state s) (inputs i) = Zmod.unsigned (N.v16 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v16 s i)) at 1; unfold R.v16, N.v16.
  rewrite ?node_14.
  unfold R.v15, N.v15.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_17 (s : N.State) (i : N.Inputs) : R.v17 (state s) (inputs i) = Zmod.unsigned (N.v17 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v17 s i)) at 1; unfold R.v17, N.v17.
  rewrite !inputs_nio_5Freq_5Fbits_5Fin1.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Freq_5Fbits_5Fin1 i)).
  finish_numeric.
Qed.
Lemma node_18 (s : N.State) (i : N.Inputs) : R.v18 (state s) (inputs i) = Zmod.unsigned (N.v18 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v18 s i)) at 1; unfold R.v18, N.v18.
  rewrite !inputs_nio_5Freq_5Fbits_5Fin1.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Freq_5Fbits_5Fin1 i)).
  finish_numeric.
Qed.
Lemma node_19 (s : N.State) (i : N.Inputs) : R.v19 (state s) (inputs i) = Zmod.unsigned (N.v19 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v19 s i)) at 1; unfold R.v19, N.v19.
  rewrite ?node_17.
  rewrite ?node_18.
  rewrite !inputs_nio_5Freq_5Fbits_5Fdw.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Freq_5Fbits_5Fdw i)).
  finish_numeric.
Qed.
Lemma node_20 (s : N.State) (i : N.Inputs) : R.v20 (state s) (inputs i) = Zmod.unsigned (N.v20 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v20 s i)) at 1; unfold R.v20, N.v20.
  rewrite ?node_16.
  rewrite ?node_19.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_21 (s : N.State) (i : N.Inputs) : R.v21 (state s) (inputs i) = Zmod.unsigned (N.v21 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v21 s i)) at 1; unfold R.v21, N.v21.
  rewrite !inputs_nio_5Freq_5Fbits_5Ffn.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Freq_5Fbits_5Ffn i)).
  finish_numeric.
Qed.
Lemma node_22 (s : N.State) (i : N.Inputs) : R.v22 (state s) (inputs i) = Zmod.unsigned (N.v22 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v22 s i)) at 1; unfold R.v22, N.v22.
  rewrite ?node_9.
  rewrite ?node_21.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_23 (s : N.State) (i : N.Inputs) : R.v23 (state s) (inputs i) = Zmod.unsigned (N.v23 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v23 s i)) at 1; unfold R.v23, N.v23.
  unfold R.v12, N.v12.
  rewrite ?node_22.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_24 (s : N.State) (i : N.Inputs) : R.v24 (state s) (inputs i) = Zmod.unsigned (N.v24 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v24 s i)) at 1; unfold R.v24, N.v24.
  rewrite ?node_13.
  rewrite ?node_23.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_25 (s : N.State) (i : N.Inputs) : R.v25 (state s) (inputs i) = Zmod.unsigned (N.v25 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v25 s i)) at 1; unfold R.v25, N.v25.
  unfold R.v15, N.v15.
  rewrite ?node_24.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_26 (s : N.State) (i : N.Inputs) : R.v26 (state s) (inputs i) = Zmod.unsigned (N.v26 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v26 s i)) at 1; unfold R.v26, N.v26.
  rewrite !inputs_nio_5Freq_5Fbits_5Fin2.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Freq_5Fbits_5Fin2 i)).
  finish_numeric.
Qed.
Lemma node_27 (s : N.State) (i : N.Inputs) : R.v27 (state s) (inputs i) = Zmod.unsigned (N.v27 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v27 s i)) at 1; unfold R.v27, N.v27.
  rewrite !inputs_nio_5Freq_5Fbits_5Fin2.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Freq_5Fbits_5Fin2 i)).
  finish_numeric.
Qed.
Lemma node_28 (s : N.State) (i : N.Inputs) : R.v28 (state s) (inputs i) = Zmod.unsigned (N.v28 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v28 s i)) at 1; unfold R.v28, N.v28.
  rewrite ?node_26.
  rewrite ?node_27.
  rewrite !inputs_nio_5Freq_5Fbits_5Fdw.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Freq_5Fbits_5Fdw i)).
  finish_numeric.
Qed.
Lemma node_29 (s : N.State) (i : N.Inputs) : R.v29 (state s) (inputs i) = Zmod.unsigned (N.v29 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v29 s i)) at 1; unfold R.v29, N.v29.
  rewrite ?node_25.
  rewrite ?node_28.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_30 (s : N.State) (i : N.Inputs) : R.v30 (state s) (inputs i) = Zmod.unsigned (N.v30 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v30 s i)) at 1; unfold R.v30, N.v30.
  rewrite ?node_20.
  rewrite ?node_29.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_31 (s : N.State) (i : N.Inputs) : R.v31 (state s) (inputs i) = Zmod.unsigned (N.v31 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v31 s i)) at 1; unfold R.v31, N.v31.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_32 (s : N.State) (i : N.Inputs) : R.v32 (state s) (inputs i) = Zmod.unsigned (N.v32 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v32 s i)) at 1; unfold R.v32, N.v32.
  rewrite ?node_30.
  unfold R.v31, N.v31.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_33 (s : N.State) (i : N.Inputs) : R.v33 (state s) (inputs i) = Zmod.unsigned (N.v33 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v33 s i)) at 1; unfold R.v33, N.v33.
  unfold R.v8, N.v8.
  unfold R.v31, N.v31.
  rewrite ?node_32.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_34 (s : N.State) (i : N.Inputs) : R.v34 (state s) (inputs i) = Zmod.unsigned (N.v34 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v34 s i)) at 1; unfold R.v34, N.v34.
  rewrite ?node_6.
  unfold R.v7, N.v7.
  rewrite ?node_33.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_35 (s : N.State) (i : N.Inputs) : R.v35 (state s) (inputs i) = Zmod.unsigned (N.v35 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v35 s i)) at 1; unfold R.v35, N.v35.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_36 (s : N.State) (i : N.Inputs) : R.v36 (state s) (inputs i) = Zmod.unsigned (N.v36 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v36 s i)) at 1; unfold R.v36, N.v36.
  unfold R.v35, N.v35.
  rewrite !state_r0_nstate.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r0_nstate s)).
  finish_numeric.
Qed.
Lemma node_37 (s : N.State) (i : N.Inputs) : R.v37 (state s) (inputs i) = Zmod.unsigned (N.v37 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v37 s i)) at 1; unfold R.v37, N.v37.
  unfold R.v4, N.v4.
  rewrite !state_r0_nstate.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r0_nstate s)).
  finish_numeric.
Qed.
Lemma node_38 (s : N.State) (i : N.Inputs) : R.v38 (state s) (inputs i) = Zmod.unsigned (N.v38 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v38 s i)) at 1; unfold R.v38, N.v38.
  rewrite ?node_36.
  rewrite ?node_37.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_39 (s : N.State) (i : N.Inputs) : R.v39 (state s) (inputs i) = Zmod.unsigned (N.v39 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v39 s i)) at 1; unfold R.v39, N.v39.
  rewrite ?node_38.
  rewrite !inputs_nio_5Fresp_5Fready.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fresp_5Fready i)).
  finish_numeric.
Qed.
Lemma node_40 (s : N.State) (i : N.Inputs) : R.v40 (state s) (inputs i) = Zmod.unsigned (N.v40 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v40 s i)) at 1; unfold R.v40, N.v40.
  rewrite ?node_39.
  rewrite !inputs_nio_5Fkill.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fkill i)).
  finish_numeric.
Qed.
Lemma node_41 (s : N.State) (i : N.Inputs) : R.v41 (state s) (inputs i) = Zmod.unsigned (N.v41 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v41 s i)) at 1; unfold R.v41, N.v41.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_42 (s : N.State) (i : N.Inputs) : R.v42 (state s) (inputs i) = Zmod.unsigned (N.v42 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v42 s i)) at 1; unfold R.v42, N.v42.
  unfold R.v41, N.v41.
  rewrite !state_r0_nstate.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r0_nstate s)).
  finish_numeric.
Qed.
Lemma node_43 (s : N.State) (i : N.Inputs) : R.v43 (state s) (inputs i) = Zmod.unsigned (N.v43 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v43 s i)) at 1; unfold R.v43, N.v43.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_44 (s : N.State) (i : N.Inputs) : R.v44 (state s) (inputs i) = Zmod.unsigned (N.v44 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v44 s i)) at 1; unfold R.v44, N.v44.
  unfold R.v43, N.v43.
  rewrite !state_r3_ncount.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r3_ncount s)).
  finish_numeric.
Qed.
Lemma node_45 (s : N.State) (i : N.Inputs) : R.v45 (state s) (inputs i) = Zmod.unsigned (N.v45 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v45 s i)) at 1; unfold R.v45, N.v45.
  rewrite ?node_42.
  rewrite ?node_44.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_46 (s : N.State) (i : N.Inputs) : R.v46 (state s) (inputs i) = Zmod.unsigned (N.v46 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v46 s i)) at 1; unfold R.v46, N.v46.
  unfold R.v31, N.v31.
  rewrite !state_r4_nneg_5Fout.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r4_nneg_5Fout s)).
  finish_numeric.
Qed.
Lemma node_47 (s : N.State) (i : N.Inputs) : R.v47 (state s) (inputs i) = Zmod.unsigned (N.v47 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v47 s i)) at 1; unfold R.v47, N.v47.
  unfold R.v31, N.v31.
  rewrite ?node_46.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_48 (s : N.State) (i : N.Inputs) : R.v48 (state s) (inputs i) = Zmod.unsigned (N.v48 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v48 s i)) at 1; unfold R.v48, N.v48.
  unfold R.v7, N.v7.
  rewrite !state_r0_nstate.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r0_nstate s)).
  finish_numeric.
Qed.
Lemma node_49 (s : N.State) (i : N.Inputs) : R.v49 (state s) (inputs i) = Zmod.unsigned (N.v49 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v49 s i)) at 1; unfold R.v49, N.v49.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_50 (s : N.State) (i : N.Inputs) : R.v50 (state s) (inputs i) = Zmod.unsigned (N.v50 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v50 s i)) at 1; unfold R.v50, N.v50.
  unfold R.v49, N.v49.
  rewrite !state_r3_ncount.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r3_ncount s)).
  finish_numeric.
Qed.
Lemma node_51 (s : N.State) (i : N.Inputs) : R.v51 (state s) (inputs i) = Zmod.unsigned (N.v51 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v51 s i)) at 1; unfold R.v51, N.v51.
  rewrite ?node_48.
  rewrite ?node_50.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_52 (s : N.State) (i : N.Inputs) : R.v52 (state s) (inputs i) = Zmod.unsigned (N.v52 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v52 s i)) at 1; unfold R.v52, N.v52.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_53 (s : N.State) (i : N.Inputs) : R.v53 (state s) (inputs i) = Zmod.unsigned (N.v53 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v53 s i)) at 1; unfold R.v53, N.v53.
  unfold R.v52, N.v52.
  rewrite !state_r0_nstate.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r0_nstate s)).
  finish_numeric.
Qed.
Lemma node_54 (s : N.State) (i : N.Inputs) : R.v54 (state s) (inputs i) = Zmod.unsigned (N.v54 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v54 s i)) at 1; unfold R.v54, N.v54.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_55 (s : N.State) (i : N.Inputs) : R.v55 (state s) (inputs i) = Zmod.unsigned (N.v55 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v55 s i)) at 1; unfold R.v55, N.v55.
  unfold R.v54, N.v54.
  rewrite !state_r0_nstate.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r0_nstate s)).
  finish_numeric.
Qed.
Lemma node_56 (s : N.State) (i : N.Inputs) : R.v56 (state s) (inputs i) = Zmod.unsigned (N.v56 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v56 s i)) at 1; unfold R.v56, N.v56.
  unfold R.v41, N.v41.
  rewrite ?node_55.
  rewrite !state_r0_nstate.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r0_nstate s)).
  finish_numeric.
Qed.
Lemma node_57 (s : N.State) (i : N.Inputs) : R.v57 (state s) (inputs i) = Zmod.unsigned (N.v57 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v57 s i)) at 1; unfold R.v57, N.v57.
  unfold R.v4, N.v4.
  rewrite ?node_53.
  rewrite ?node_56.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_58 (s : N.State) (i : N.Inputs) : R.v58 (state s) (inputs i) = Zmod.unsigned (N.v58 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v58 s i)) at 1; unfold R.v58, N.v58.
  unfold R.v35, N.v35.
  rewrite ?node_51.
  rewrite ?node_57.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_59 (s : N.State) (i : N.Inputs) : R.v59 (state s) (inputs i) = Zmod.unsigned (N.v59 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v59 s i)) at 1; unfold R.v59, N.v59.
  rewrite ?node_45.
  rewrite ?node_47.
  rewrite ?node_58.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_60 (s : N.State) (i : N.Inputs) : R.v60 (state s) (inputs i) = Zmod.unsigned (N.v60 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v60 s i)) at 1; unfold R.v60, N.v60.
  unfold R.v0, N.v0.
  rewrite ?node_40.
  rewrite ?node_59.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_61 (s : N.State) (i : N.Inputs) : R.v61 (state s) (inputs i) = Zmod.unsigned (N.v61 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v61 s i)) at 1; unfold R.v61, N.v61.
  rewrite ?node_2.
  rewrite ?node_34.
  rewrite ?node_60.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_62 (s : N.State) (i : N.Inputs) : R.v62 (state s) (inputs i) = Zmod.unsigned (N.v62 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v62 s i)) at 1; unfold R.v62, N.v62.
  rewrite ?node_2.
  rewrite !inputs_nio_5Freq_5Fbits_5Fdw.
  rewrite !state_r1_nreq_5Fdw.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Freq_5Fbits_5Fdw i)).
  rewrite ?(bits.mod_to_Z (N.r1_nreq_5Fdw s)).
  finish_numeric.
Qed.
Lemma node_63 (s : N.State) (i : N.Inputs) : R.v63 (state s) (inputs i) = Zmod.unsigned (N.v63 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v63 s i)) at 1; unfold R.v63, N.v63.
  rewrite ?node_2.
  rewrite !inputs_nio_5Freq_5Fbits_5Ftag.
  rewrite !state_r2_nreq_5Ftag.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Freq_5Fbits_5Ftag i)).
  rewrite ?(bits.mod_to_Z (N.r2_nreq_5Ftag s)).
  finish_numeric.
Qed.
Lemma node_64 (s : N.State) (i : N.Inputs) : R.v64 (state s) (inputs i) = Zmod.unsigned (N.v64 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v64 s i)) at 1; unfold R.v64, N.v64.
  unfold R.v31, N.v31.
  rewrite !inputs_nio_5Freq_5Fbits_5Fdw.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Freq_5Fbits_5Fdw i)).
  finish_numeric.
Qed.
Lemma node_65 (s : N.State) (i : N.Inputs) : R.v65 (state s) (inputs i) = Zmod.unsigned (N.v65 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v65 s i)) at 1; unfold R.v65, N.v65.
  rewrite ?node_6.
  rewrite ?node_64.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_66 (s : N.State) (i : N.Inputs) : R.v66 (state s) (inputs i) = Zmod.unsigned (N.v66 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v66 s i)) at 1; unfold R.v66, N.v66.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_67 (s : N.State) (i : N.Inputs) : R.v67 (state s) (inputs i) = Zmod.unsigned (N.v67 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v67 s i)) at 1; unfold R.v67, N.v67.
  unfold R.v8, N.v8.
  rewrite ?node_65.
  unfold R.v66, N.v66.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_68 (s : N.State) (i : N.Inputs) : R.v68 (state s) (inputs i) = Zmod.unsigned (N.v68 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v68 s i)) at 1; unfold R.v68, N.v68.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_69 (s : N.State) (i : N.Inputs) : R.v69 (state s) (inputs i) = Zmod.unsigned (N.v69 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v69 s i)) at 1; unfold R.v69, N.v69.
  unfold R.v68, N.v68.
  rewrite !state_r3_ncount.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r3_ncount s)).
  finish_numeric.
Qed.
Lemma node_70 (s : N.State) (i : N.Inputs) : R.v70 (state s) (inputs i) = Zmod.unsigned (N.v70 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v70 s i)) at 1; unfold R.v70, N.v70.
  unfold R.v68, N.v68.
  rewrite !state_r3_ncount.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r3_ncount s)).
  finish_numeric.
Qed.
Lemma node_71 (s : N.State) (i : N.Inputs) : R.v71 (state s) (inputs i) = Zmod.unsigned (N.v71 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v71 s i)) at 1; unfold R.v71, N.v71.
  rewrite ?node_48.
  rewrite ?node_70.
  rewrite !state_r3_ncount.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r3_ncount s)).
  finish_numeric.
Qed.
Lemma node_72 (s : N.State) (i : N.Inputs) : R.v72 (state s) (inputs i) = Zmod.unsigned (N.v72 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v72 s i)) at 1; unfold R.v72, N.v72.
  rewrite ?node_42.
  rewrite ?node_69.
  rewrite ?node_71.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_73 (s : N.State) (i : N.Inputs) : R.v73 (state s) (inputs i) = Zmod.unsigned (N.v73 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v73 s i)) at 1; unfold R.v73, N.v73.
  rewrite ?node_2.
  rewrite ?node_67.
  rewrite ?node_72.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_74 (s : N.State) (i : N.Inputs) : R.v74 (state s) (inputs i) = Zmod.unsigned (N.v74 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v74 s i)) at 1; unfold R.v74, N.v74.
  rewrite !inputs_nio_5Freq_5Fbits_5Ffn.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Freq_5Fbits_5Ffn i)).
  finish_numeric.
Qed.
Lemma node_75 (s : N.State) (i : N.Inputs) : R.v75 (state s) (inputs i) = Zmod.unsigned (N.v75 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v75 s i)) at 1; unfold R.v75, N.v75.
  rewrite ?node_6.
  rewrite ?node_74.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_76 (s : N.State) (i : N.Inputs) : R.v76 (state s) (inputs i) = Zmod.unsigned (N.v76 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v76 s i)) at 1; unfold R.v76, N.v76.
  unfold R.v12, N.v12.
  rewrite ?node_75.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_77 (s : N.State) (i : N.Inputs) : R.v77 (state s) (inputs i) = Zmod.unsigned (N.v77 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v77 s i)) at 1; unfold R.v77, N.v77.
  rewrite !inputs_nio_5Freq_5Fbits_5Ffn.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Freq_5Fbits_5Ffn i)).
  finish_numeric.
Qed.
Lemma node_78 (s : N.State) (i : N.Inputs) : R.v78 (state s) (inputs i) = Zmod.unsigned (N.v78 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v78 s i)) at 1; unfold R.v78, N.v78.
  rewrite ?node_76.
  rewrite ?node_77.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_79 (s : N.State) (i : N.Inputs) : R.v79 (state s) (inputs i) = Zmod.unsigned (N.v79 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v79 s i)) at 1; unfold R.v79, N.v79.
  unfold R.v15, N.v15.
  rewrite ?node_78.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_80 (s : N.State) (i : N.Inputs) : R.v80 (state s) (inputs i) = Zmod.unsigned (N.v80 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v80 s i)) at 1; unfold R.v80, N.v80.
  rewrite ?node_20.
  rewrite ?node_29.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_81 (s : N.State) (i : N.Inputs) : R.v81 (state s) (inputs i) = Zmod.unsigned (N.v81 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v81 s i)) at 1; unfold R.v81, N.v81.
  rewrite ?node_20.
  rewrite ?node_79.
  rewrite ?node_80.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_82 (s : N.State) (i : N.Inputs) : R.v82 (state s) (inputs i) = Zmod.unsigned (N.v82 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v82 s i)) at 1; unfold R.v82, N.v82.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_83 (s : N.State) (i : N.Inputs) : R.v83 (state s) (inputs i) = Zmod.unsigned (N.v83 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v83 s i)) at 1; unfold R.v83, N.v83.
  unfold R.v82, N.v82.
  rewrite !state_r3_ncount.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r3_ncount s)).
  finish_numeric.
Qed.
Lemma node_84 (s : N.State) (i : N.Inputs) : R.v84 (state s) (inputs i) = Zmod.unsigned (N.v84 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v84 s i)) at 1; unfold R.v84, N.v84.
  rewrite !state_r8_nremainder.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r8_nremainder s)).
  finish_numeric.
Qed.
Lemma node_85 (s : N.State) (i : N.Inputs) : R.v85 (state s) (inputs i) = Zmod.unsigned (N.v85 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v85 s i)) at 1; unfold R.v85, N.v85.
  rewrite ?node_84.
  rewrite !state_r7_ndivisor.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r7_ndivisor s)).
  finish_numeric.
Qed.
Lemma node_86 (s : N.State) (i : N.Inputs) : R.v86 (state s) (inputs i) = Zmod.unsigned (N.v86 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v86 s i)) at 1; unfold R.v86, N.v86.
  rewrite ?node_85.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_87 (s : N.State) (i : N.Inputs) : R.v87 (state s) (inputs i) = Zmod.unsigned (N.v87 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v87 s i)) at 1; unfold R.v87, N.v87.
  unfold R.v31, N.v31.
  rewrite ?node_86.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_88 (s : N.State) (i : N.Inputs) : R.v88 (state s) (inputs i) = Zmod.unsigned (N.v88 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v88 s i)) at 1; unfold R.v88, N.v88.
  unfold R.v31, N.v31.
  rewrite !state_r5_nisHi.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nisHi s)).
  finish_numeric.
Qed.
Lemma node_89 (s : N.State) (i : N.Inputs) : R.v89 (state s) (inputs i) = Zmod.unsigned (N.v89 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v89 s i)) at 1; unfold R.v89, N.v89.
  rewrite ?node_42.
  rewrite ?node_83.
  rewrite ?node_87.
  rewrite ?node_88.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_90 (s : N.State) (i : N.Inputs) : R.v90 (state s) (inputs i) = Zmod.unsigned (N.v90 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v90 s i)) at 1; unfold R.v90, N.v90.
  unfold R.v31, N.v31.
  rewrite ?node_89.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_91 (s : N.State) (i : N.Inputs) : R.v91 (state s) (inputs i) = Zmod.unsigned (N.v91 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v91 s i)) at 1; unfold R.v91, N.v91.
  rewrite ?node_90.
  rewrite !state_r4_nneg_5Fout.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r4_nneg_5Fout s)).
  finish_numeric.
Qed.
Lemma node_92 (s : N.State) (i : N.Inputs) : R.v92 (state s) (inputs i) = Zmod.unsigned (N.v92 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v92 s i)) at 1; unfold R.v92, N.v92.
  rewrite ?node_2.
  rewrite ?node_81.
  rewrite ?node_91.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_93 (s : N.State) (i : N.Inputs) : R.v93 (state s) (inputs i) = Zmod.unsigned (N.v93 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v93 s i)) at 1; unfold R.v93, N.v93.
  rewrite ?node_2.
  rewrite ?node_79.
  rewrite !state_r5_nisHi.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nisHi s)).
  finish_numeric.
Qed.
Lemma node_94 (s : N.State) (i : N.Inputs) : R.v94 (state s) (inputs i) = Zmod.unsigned (N.v94 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v94 s i)) at 1; unfold R.v94, N.v94.
  rewrite ?node_2.
  unfold R.v31, N.v31.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_95 (s : N.State) (i : N.Inputs) : R.v95 (state s) (inputs i) = Zmod.unsigned (N.v95 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v95 s i)) at 1; unfold R.v95, N.v95.
  rewrite ?node_42.
  rewrite ?node_44.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_96 (s : N.State) (i : N.Inputs) : R.v96 (state s) (inputs i) = Zmod.unsigned (N.v96 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v96 s i)) at 1; unfold R.v96, N.v96.
  rewrite ?node_51.
  rewrite ?node_95.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_97 (s : N.State) (i : N.Inputs) : R.v97 (state s) (inputs i) = Zmod.unsigned (N.v97 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v97 s i)) at 1; unfold R.v97, N.v97.
  unfold R.v31, N.v31.
  rewrite ?node_53.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_98 (s : N.State) (i : N.Inputs) : R.v98 (state s) (inputs i) = Zmod.unsigned (N.v98 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v98 s i)) at 1; unfold R.v98, N.v98.
  rewrite ?node_97.
  rewrite !state_r6_nresHi.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_nresHi s)).
  finish_numeric.
Qed.
Lemma node_99 (s : N.State) (i : N.Inputs) : R.v99 (state s) (inputs i) = Zmod.unsigned (N.v99 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v99 s i)) at 1; unfold R.v99, N.v99.
  rewrite ?node_96.
  rewrite ?node_98.
  rewrite !state_r5_nisHi.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nisHi s)).
  finish_numeric.
Qed.
Lemma node_100 (s : N.State) (i : N.Inputs) : R.v100 (state s) (inputs i) = Zmod.unsigned (N.v100 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v100 s i)) at 1; unfold R.v100, N.v100.
  rewrite ?node_94.
  rewrite ?node_99.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_101 (s : N.State) (i : N.Inputs) : R.v101 (state s) (inputs i) = Zmod.unsigned (N.v101 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v101 s i)) at 1; unfold R.v101, N.v101.
  rewrite !inputs_nio_5Freq_5Fbits_5Fin2.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Freq_5Fbits_5Fin2 i)).
  finish_numeric.
Qed.
Lemma node_102 (s : N.State) (i : N.Inputs) : R.v102 (state s) (inputs i) = Zmod.unsigned (N.v102 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v102 s i)) at 1; unfold R.v102, N.v102.
  rewrite ?node_29.
  unfold RB.word.
  rewrite repeat_32, bits.mod_to_Z; reflexivity.
Qed.
Lemma node_103 (s : N.State) (i : N.Inputs) : R.v103 (state s) (inputs i) = Zmod.unsigned (N.v103 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v103 s i)) at 1; unfold R.v103, N.v103.
  rewrite ?node_101.
  rewrite ?node_102.
  rewrite !inputs_nio_5Freq_5Fbits_5Fdw.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Freq_5Fbits_5Fdw i)).
  finish_numeric.
Qed.
Lemma node_104 (s : N.State) (i : N.Inputs) : R.v104 (state s) (inputs i) = Zmod.unsigned (N.v104 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v104 s i)) at 1; unfold R.v104, N.v104.
  rewrite !inputs_nio_5Freq_5Fbits_5Fin2.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Freq_5Fbits_5Fin2 i)).
  finish_numeric.
Qed.
Lemma node_105 (s : N.State) (i : N.Inputs) : R.v105 (state s) (inputs i) = Zmod.unsigned (N.v105 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v105 s i)) at 1; unfold R.v105, N.v105.
  rewrite ?node_29.
  rewrite ?node_103.
  rewrite ?node_104.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_106 (s : N.State) (i : N.Inputs) : R.v106 (state s) (inputs i) = Zmod.unsigned (N.v106 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v106 s i)) at 1; unfold R.v106, N.v106.
  rewrite !state_r7_ndivisor.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r7_ndivisor s)).
  finish_numeric.
Qed.
Lemma node_107 (s : N.State) (i : N.Inputs) : R.v107 (state s) (inputs i) = Zmod.unsigned (N.v107 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v107 s i)) at 1; unfold R.v107, N.v107.
  rewrite ?node_55.
  rewrite ?node_106.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_108 (s : N.State) (i : N.Inputs) : R.v108 (state s) (inputs i) = Zmod.unsigned (N.v108 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v108 s i)) at 1; unfold R.v108, N.v108.
  rewrite ?node_85.
  rewrite ?node_107.
  rewrite !state_r7_ndivisor.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r7_ndivisor s)).
  finish_numeric.
Qed.
Lemma node_109 (s : N.State) (i : N.Inputs) : R.v109 (state s) (inputs i) = Zmod.unsigned (N.v109 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v109 s i)) at 1; unfold R.v109, N.v109.
  rewrite ?node_2.
  rewrite ?node_105.
  rewrite ?node_108.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_110 (s : N.State) (i : N.Inputs) : R.v110 (state s) (inputs i) = Zmod.unsigned (N.v110 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v110 s i)) at 1; unfold R.v110, N.v110.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_111 (s : N.State) (i : N.Inputs) : R.v111 (state s) (inputs i) = Zmod.unsigned (N.v111 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v111 s i)) at 1; unfold R.v111, N.v111.
  rewrite !inputs_nio_5Freq_5Fbits_5Fin1.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Freq_5Fbits_5Fin1 i)).
  finish_numeric.
Qed.
Lemma node_112 (s : N.State) (i : N.Inputs) : R.v112 (state s) (inputs i) = Zmod.unsigned (N.v112 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v112 s i)) at 1; unfold R.v112, N.v112.
  rewrite ?node_20.
  unfold RB.word.
  rewrite repeat_32, bits.mod_to_Z; reflexivity.
Qed.
Lemma node_113 (s : N.State) (i : N.Inputs) : R.v113 (state s) (inputs i) = Zmod.unsigned (N.v113 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v113 s i)) at 1; unfold R.v113, N.v113.
  rewrite ?node_111.
  rewrite ?node_112.
  rewrite !inputs_nio_5Freq_5Fbits_5Fdw.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Freq_5Fbits_5Fdw i)).
  finish_numeric.
Qed.
Lemma node_114 (s : N.State) (i : N.Inputs) : R.v114 (state s) (inputs i) = Zmod.unsigned (N.v114 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v114 s i)) at 1; unfold R.v114, N.v114.
  rewrite !inputs_nio_5Freq_5Fbits_5Fin1.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Freq_5Fbits_5Fin1 i)).
  finish_numeric.
Qed.
Lemma node_115 (s : N.State) (i : N.Inputs) : R.v115 (state s) (inputs i) = Zmod.unsigned (N.v115 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v115 s i)) at 1; unfold R.v115, N.v115.
  unfold R.v110, N.v110.
  rewrite ?node_113.
  rewrite ?node_114.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_116 (s : N.State) (i : N.Inputs) : R.v116 (state s) (inputs i) = Zmod.unsigned (N.v116 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v116 s i)) at 1; unfold R.v116, N.v116.
  rewrite !state_r8_nremainder.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r8_nremainder s)).
  finish_numeric.
Qed.
Lemma node_117 (s : N.State) (i : N.Inputs) : R.v117 (state s) (inputs i) = Zmod.unsigned (N.v117 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v117 s i)) at 1; unfold R.v117, N.v117.
  rewrite ?node_85.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_118 (s : N.State) (i : N.Inputs) : R.v118 (state s) (inputs i) = Zmod.unsigned (N.v118 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v118 s i)) at 1; unfold R.v118, N.v118.
  rewrite ?node_86.
  rewrite ?node_116.
  rewrite ?node_117.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_119 (s : N.State) (i : N.Inputs) : R.v119 (state s) (inputs i) = Zmod.unsigned (N.v119 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v119 s i)) at 1; unfold R.v119, N.v119.
  rewrite !state_r8_nremainder.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r8_nremainder s)).
  finish_numeric.
Qed.
Lemma node_120 (s : N.State) (i : N.Inputs) : R.v120 (state s) (inputs i) = Zmod.unsigned (N.v120 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v120 s i)) at 1; unfold R.v120, N.v120.
  unfold R.v31, N.v31.
  rewrite ?node_86.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_121 (s : N.State) (i : N.Inputs) : R.v121 (state s) (inputs i) = Zmod.unsigned (N.v121 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v121 s i)) at 1; unfold R.v121, N.v121.
  unfold R.v8, N.v8.
  rewrite ?node_118.
  rewrite ?node_119.
  rewrite ?node_120.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_122 (s : N.State) (i : N.Inputs) : R.v122 (state s) (inputs i) = Zmod.unsigned (N.v122 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v122 s i)) at 1; unfold R.v122, N.v122.
  rewrite !state_r8_nremainder.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r8_nremainder s)).
  finish_numeric.
Qed.
Lemma node_123 (s : N.State) (i : N.Inputs) : R.v123 (state s) (inputs i) = Zmod.unsigned (N.v123 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v123 s i)) at 1; unfold R.v123, N.v123.
  rewrite ?node_122.
  unfold RB.word.
  rewrite repeat_65, bits.mod_to_Z; reflexivity.
Qed.
Lemma node_124 (s : N.State) (i : N.Inputs) : R.v124 (state s) (inputs i) = Zmod.unsigned (N.v124 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v124 s i)) at 1; unfold R.v124, N.v124.
  rewrite !state_r8_nremainder.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r8_nremainder s)).
  finish_numeric.
Qed.
Lemma node_125 (s : N.State) (i : N.Inputs) : R.v125 (state s) (inputs i) = Zmod.unsigned (N.v125 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v125 s i)) at 1; unfold R.v125, N.v125.
  rewrite ?node_123.
  rewrite ?node_124.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_126 (s : N.State) (i : N.Inputs) : R.v126 (state s) (inputs i) = Zmod.unsigned (N.v126 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v126 s i)) at 1; unfold R.v126, N.v126.
  rewrite !state_r7_ndivisor.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r7_ndivisor s)).
  finish_numeric.
Qed.
Lemma node_127 (s : N.State) (i : N.Inputs) : R.v127 (state s) (inputs i) = Zmod.unsigned (N.v127 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v127 s i)) at 1; unfold R.v127, N.v127.
  rewrite ?node_126.
  rewrite !state_r7_ndivisor.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r7_ndivisor s)).
  finish_numeric.
Qed.
Lemma node_128 (s : N.State) (i : N.Inputs) : R.v128 (state s) (inputs i) = Zmod.unsigned (N.v128 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v128 s i)) at 1; unfold R.v128, N.v128.
  rewrite ?node_125.
  rewrite ?node_127.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_129 (s : N.State) (i : N.Inputs) : R.v129 (state s) (inputs i) = Zmod.unsigned (N.v129 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v129 s i)) at 1; unfold R.v129, N.v129.
  rewrite !state_r8_nremainder.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r8_nremainder s)).
  finish_numeric.
Qed.
Lemma node_130 (s : N.State) (i : N.Inputs) : R.v130 (state s) (inputs i) = Zmod.unsigned (N.v130 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v130 s i)) at 1; unfold R.v130, N.v130.
  rewrite !state_r8_nremainder.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r8_nremainder s)).
  finish_numeric.
Qed.
Lemma node_131 (s : N.State) (i : N.Inputs) : R.v131 (state s) (inputs i) = Zmod.unsigned (N.v131 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v131 s i)) at 1; unfold R.v131, N.v131.
  rewrite ?node_129.
  rewrite ?node_130.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_132 (s : N.State) (i : N.Inputs) : R.v132 (state s) (inputs i) = Zmod.unsigned (N.v132 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v132 s i)) at 1; unfold R.v132, N.v132.
  rewrite ?node_128.
  rewrite ?node_131.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_133 (s : N.State) (i : N.Inputs) : R.v133 (state s) (inputs i) = Zmod.unsigned (N.v133 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v133 s i)) at 1; unfold R.v133, N.v133.
  rewrite ?node_132.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_134 (s : N.State) (i : N.Inputs) : R.v134 (state s) (inputs i) = Zmod.unsigned (N.v134 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v134 s i)) at 1; unfold R.v134, N.v134.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_135 (s : N.State) (i : N.Inputs) : R.v135 (state s) (inputs i) = Zmod.unsigned (N.v135 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v135 s i)) at 1; unfold R.v135, N.v135.
  unfold R.v134, N.v134.
  rewrite !state_r3_ncount.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r3_ncount s)).
  finish_numeric.
Qed.
Lemma node_136 (s : N.State) (i : N.Inputs) : R.v136 (state s) (inputs i) = Zmod.unsigned (N.v136 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v136 s i)) at 1; unfold R.v136, N.v136.
  rewrite ?node_135.
  rewrite !state_r4_nneg_5Fout.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r4_nneg_5Fout s)).
  finish_numeric.
Qed.
Lemma node_137 (s : N.State) (i : N.Inputs) : R.v137 (state s) (inputs i) = Zmod.unsigned (N.v137 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v137 s i)) at 1; unfold R.v137, N.v137.
  rewrite ?node_132.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_138 (s : N.State) (i : N.Inputs) : R.v138 (state s) (inputs i) = Zmod.unsigned (N.v138 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v138 s i)) at 1; unfold R.v138, N.v138.
  rewrite !state_r8_nremainder.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r8_nremainder s)).
  finish_numeric.
Qed.
Lemma node_139 (s : N.State) (i : N.Inputs) : R.v139 (state s) (inputs i) = Zmod.unsigned (N.v139 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v139 s i)) at 1; unfold R.v139, N.v139.
  rewrite ?node_133.
  rewrite ?node_136.
  rewrite ?node_137.
  rewrite ?node_138.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_140 (s : N.State) (i : N.Inputs) : R.v140 (state s) (inputs i) = Zmod.unsigned (N.v140 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v140 s i)) at 1; unfold R.v140, N.v140.
  rewrite !state_r8_nremainder.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r8_nremainder s)).
  finish_numeric.
Qed.
Lemma node_141 (s : N.State) (i : N.Inputs) : R.v141 (state s) (inputs i) = Zmod.unsigned (N.v141 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v141 s i)) at 1; unfold R.v141, N.v141.
  rewrite ?node_55.
  rewrite ?node_140.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_142 (s : N.State) (i : N.Inputs) : R.v142 (state s) (inputs i) = Zmod.unsigned (N.v142 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v142 s i)) at 1; unfold R.v142, N.v142.
  rewrite ?node_53.
  rewrite ?node_141.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_143 (s : N.State) (i : N.Inputs) : R.v143 (state s) (inputs i) = Zmod.unsigned (N.v143 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v143 s i)) at 1; unfold R.v143, N.v143.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_144 (s : N.State) (i : N.Inputs) : R.v144 (state s) (inputs i) = Zmod.unsigned (N.v144 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v144 s i)) at 1; unfold R.v144, N.v144.
  rewrite !state_r8_nremainder.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r8_nremainder s)).
  finish_numeric.
Qed.
Lemma node_145 (s : N.State) (i : N.Inputs) : R.v145 (state s) (inputs i) = Zmod.unsigned (N.v145 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v145 s i)) at 1; unfold R.v145, N.v145.
  rewrite ?node_119.
  rewrite ?node_144.
  rewrite !state_r6_nresHi.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_nresHi s)).
  finish_numeric.
Qed.
Lemma node_146 (s : N.State) (i : N.Inputs) : R.v146 (state s) (inputs i) = Zmod.unsigned (N.v146 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v146 s i)) at 1; unfold R.v146, N.v146.
  unfold R.v143, N.v143.
  rewrite ?node_145.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_147 (s : N.State) (i : N.Inputs) : R.v147 (state s) (inputs i) = Zmod.unsigned (N.v147 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v147 s i)) at 1; unfold R.v147, N.v147.
  unfold R.v110, N.v110.
  rewrite ?node_146.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_148 (s : N.State) (i : N.Inputs) : R.v148 (state s) (inputs i) = Zmod.unsigned (N.v148 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v148 s i)) at 1; unfold R.v148, N.v148.
  rewrite ?node_142.
  rewrite ?node_147.
  rewrite !state_r8_nremainder.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r8_nremainder s)).
  finish_numeric.
Qed.
Lemma node_149 (s : N.State) (i : N.Inputs) : R.v149 (state s) (inputs i) = Zmod.unsigned (N.v149 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v149 s i)) at 1; unfold R.v149, N.v149.
  rewrite ?node_48.
  rewrite ?node_139.
  rewrite ?node_148.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_150 (s : N.State) (i : N.Inputs) : R.v150 (state s) (inputs i) = Zmod.unsigned (N.v150 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v150 s i)) at 1; unfold R.v150, N.v150.
  rewrite ?node_42.
  rewrite ?node_121.
  rewrite ?node_149.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_151 (s : N.State) (i : N.Inputs) : R.v151 (state s) (inputs i) = Zmod.unsigned (N.v151 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v151 s i)) at 1; unfold R.v151, N.v151.
  rewrite ?node_2.
  rewrite ?node_115.
  rewrite ?node_150.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_152 (s : N.State) (i : N.Inputs) : R.v152 (state s) (inputs i) = Zmod.unsigned (N.v152 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v152 s i)) at 1; unfold R.v152, N.v152.
  rewrite ?node_145.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_153 (s : N.State) (i : N.Inputs) : R.v153 (state s) (inputs i) = Zmod.unsigned (N.v153 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v153 s i)) at 1; unfold R.v153, N.v153.
  rewrite !state_r0_nstate.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r0_nstate s)).
  finish_numeric.
Qed.
Lemma node_154 (s : N.State) (i : N.Inputs) : R.v154 (state s) (inputs i) = Zmod.unsigned (N.v154 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v154 s i)) at 1; unfold R.v154, N.v154.
  rewrite ?node_153.
  rewrite !state_r1_nreq_5Fdw.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r1_nreq_5Fdw s)).
  finish_numeric.
Qed.
Lemma node_155 (s : N.State) (i : N.Inputs) : R.v155 (state s) (inputs i) = Zmod.unsigned (N.v155 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v155 s i)) at 1; unfold R.v155, N.v155.
  rewrite ?node_145.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_156 (s : N.State) (i : N.Inputs) : R.v156 (state s) (inputs i) = Zmod.unsigned (N.v156 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v156 s i)) at 1; unfold R.v156, N.v156.
  rewrite ?node_152.
  rewrite ?node_154.
  rewrite ?node_155.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_157 (s : N.State) (i : N.Inputs) : R.v157 (state s) (inputs i) = Zmod.unsigned (N.v157 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v157 s i)) at 1; unfold R.v157, N.v157.
  rewrite ?node_156.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_158 (s : N.State) (i : N.Inputs) : R.v158 (state s) (inputs i) = Zmod.unsigned (N.v158 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v158 s i)) at 1; unfold R.v158, N.v158.
  rewrite ?node_157.
  unfold RB.word.
  rewrite repeat_32, bits.mod_to_Z; reflexivity.
Qed.
Lemma node_159 (s : N.State) (i : N.Inputs) : R.v159 (state s) (inputs i) = Zmod.unsigned (N.v159 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v159 s i)) at 1; unfold R.v159, N.v159.
  rewrite ?node_152.
  rewrite ?node_158.
  rewrite !state_r1_nreq_5Fdw.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r1_nreq_5Fdw s)).
  finish_numeric.
Qed.
Lemma node_160 (s : N.State) (i : N.Inputs) : R.v160 (state s) (inputs i) = Zmod.unsigned (N.v160 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v160 s i)) at 1; unfold R.v160, N.v160.
  rewrite ?node_156.
  rewrite ?node_159.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma state_ext (a b : R.State) :
  R.r0_nstate a = R.r0_nstate b ->
  R.r1_nreq_5Fdw a = R.r1_nreq_5Fdw b ->
  R.r2_nreq_5Ftag a = R.r2_nreq_5Ftag b ->
  R.r3_ncount a = R.r3_ncount b ->
  R.r4_nneg_5Fout a = R.r4_nneg_5Fout b ->
  R.r5_nisHi a = R.r5_nisHi b ->
  R.r6_nresHi a = R.r6_nresHi b ->
  R.r7_ndivisor a = R.r7_ndivisor b ->
  R.r8_nremainder a = R.r8_nremainder b ->
  a = b.
Proof. destruct a, b; cbn; intros; subst; reflexivity. Qed.
Lemma outputs_ext (a b : R.Outputs) :
  R.nio_5Freq_5Fready a = R.nio_5Freq_5Fready b ->
  R.nio_5Fresp_5Fvalid a = R.nio_5Fresp_5Fvalid b ->
  R.nio_5Fresp_5Fbits_5Fdata a = R.nio_5Fresp_5Fbits_5Fdata b ->
  R.nio_5Fresp_5Fbits_5Ftag a = R.nio_5Fresp_5Fbits_5Ftag b ->
  a = b.
Proof. destruct a, b; cbn; intros; subst; reflexivity. Qed.
Theorem step_refines (s : N.State) (i : N.Inputs) : state (N.step s i) = R.step (state s) (inputs i).
Proof. apply state_ext.
  - rewrite state_r0_nstate.
    change (Zmod.unsigned (if Zmod.eqb (N.nreset i) Zmod.one then N.v0 s i else N.v61 s i) =
      if Z.eqb (Zmod.unsigned (N.nreset i) mod 2^1) 1 then R.v0 (state s) (inputs i) else R.v61 (state s) (inputs i)).
    rewrite bits.mod_to_Z, node_0, node_61; finish_numeric.
  - rewrite state_r1_nreq_5Fdw.
    change (Zmod.unsigned (N.v62 s i) = R.v62 (state s) (inputs i)); symmetry; exact (node_62 s i).
  - rewrite state_r2_nreq_5Ftag.
    change (Zmod.unsigned (N.v63 s i) = R.v63 (state s) (inputs i)); symmetry; exact (node_63 s i).
  - rewrite state_r3_ncount.
    change (Zmod.unsigned (N.v73 s i) = R.v73 (state s) (inputs i)); symmetry; exact (node_73 s i).
  - rewrite state_r4_nneg_5Fout.
    change (Zmod.unsigned (N.v92 s i) = R.v92 (state s) (inputs i)); symmetry; exact (node_92 s i).
  - rewrite state_r5_nisHi.
    change (Zmod.unsigned (N.v93 s i) = R.v93 (state s) (inputs i)); symmetry; exact (node_93 s i).
  - rewrite state_r6_nresHi.
    change (Zmod.unsigned (N.v100 s i) = R.v100 (state s) (inputs i)); symmetry; exact (node_100 s i).
  - rewrite state_r7_ndivisor.
    change (Zmod.unsigned (N.v109 s i) = R.v109 (state s) (inputs i)); symmetry; exact (node_109 s i).
  - rewrite state_r8_nremainder.
    change (Zmod.unsigned (N.v151 s i) = R.v151 (state s) (inputs i)); symmetry; exact (node_151 s i).
Qed.
Theorem run_refines (s : N.State) (pins : nat -> N.Inputs) t : state (N.run s pins t) = R.run (state s) (fun k => inputs (pins k)) t.
Proof. induction t; cbn [N.run R.run]; [reflexivity | rewrite step_refines, IHt; reflexivity]. Qed.
Lemma output_nio_5Freq_5Fready s i : R.nio_5Freq_5Fready (R.observe (state s) (inputs i)) = Zmod.unsigned (N.nio_5Freq_5Fready (N.observe s i)).
Proof.
  exact (node_1 s i).
Qed.
Lemma output_nio_5Fresp_5Fvalid s i : R.nio_5Fresp_5Fvalid (R.observe (state s) (inputs i)) = Zmod.unsigned (N.nio_5Fresp_5Fvalid (N.observe s i)).
Proof.
  exact (node_38 s i).
Qed.
Lemma output_nio_5Fresp_5Fbits_5Fdata s i : R.nio_5Fresp_5Fbits_5Fdata (R.observe (state s) (inputs i)) = Zmod.unsigned (N.nio_5Fresp_5Fbits_5Fdata (N.observe s i)).
Proof.
  exact (node_160 s i).
Qed.
Lemma output_nio_5Fresp_5Fbits_5Ftag s i : R.nio_5Fresp_5Fbits_5Ftag (R.observe (state s) (inputs i)) = Zmod.unsigned (N.nio_5Fresp_5Fbits_5Ftag (N.observe s i)).
Proof.
  change (RB.word 5 (R.r2_nreq_5Ftag (state s)) = Zmod.unsigned (N.r2_nreq_5Ftag s)).
  rewrite state_r2_nreq_5Ftag; unfold RB.word; apply bits.mod_to_Z.
Qed.
Theorem observe_refines s i : outputs (N.observe s i) = R.observe (state s) (inputs i).
Proof. apply outputs_ext.
  - rewrite outputs_nio_5Freq_5Fready; symmetry; apply output_nio_5Freq_5Fready.
  - rewrite outputs_nio_5Fresp_5Fvalid; symmetry; apply output_nio_5Fresp_5Fvalid.
  - rewrite outputs_nio_5Fresp_5Fbits_5Fdata; symmetry; apply output_nio_5Fresp_5Fbits_5Fdata.
  - rewrite outputs_nio_5Fresp_5Fbits_5Ftag; symmetry; apply output_nio_5Fresp_5Fbits_5Ftag.
Qed.
Local Opaque R.v0 N.v0 R.v1 N.v1 R.v2 N.v2 R.v3 N.v3 R.v4 N.v4 R.v5 N.v5 R.v6 N.v6 R.v7 N.v7 R.v8 N.v8 R.v9 N.v9 R.v10 N.v10 R.v11 N.v11 R.v12 N.v12 R.v13 N.v13 R.v14 N.v14 R.v15 N.v15 R.v16 N.v16 R.v17 N.v17 R.v18 N.v18 R.v19 N.v19 R.v20 N.v20 R.v21 N.v21 R.v22 N.v22 R.v23 N.v23 R.v24 N.v24 R.v25 N.v25 R.v26 N.v26 R.v27 N.v27 R.v28 N.v28 R.v29 N.v29 R.v30 N.v30 R.v31 N.v31 R.v32 N.v32 R.v33 N.v33 R.v34 N.v34 R.v35 N.v35 R.v36 N.v36 R.v37 N.v37 R.v38 N.v38 R.v39 N.v39 R.v40 N.v40 R.v41 N.v41 R.v42 N.v42 R.v43 N.v43 R.v44 N.v44 R.v45 N.v45 R.v46 N.v46 R.v47 N.v47 R.v48 N.v48 R.v49 N.v49 R.v50 N.v50 R.v51 N.v51 R.v52 N.v52 R.v53 N.v53 R.v54 N.v54 R.v55 N.v55 R.v56 N.v56 R.v57 N.v57 R.v58 N.v58 R.v59 N.v59 R.v60 N.v60 R.v61 N.v61 R.v62 N.v62 R.v63 N.v63 R.v64 N.v64 R.v65 N.v65 R.v66 N.v66 R.v67 N.v67 R.v68 N.v68 R.v69 N.v69 R.v70 N.v70 R.v71 N.v71 R.v72 N.v72 R.v73 N.v73 R.v74 N.v74 R.v75 N.v75 R.v76 N.v76 R.v77 N.v77 R.v78 N.v78 R.v79 N.v79 R.v80 N.v80 R.v81 N.v81 R.v82 N.v82 R.v83 N.v83 R.v84 N.v84 R.v85 N.v85 R.v86 N.v86 R.v87 N.v87 R.v88 N.v88 R.v89 N.v89 R.v90 N.v90 R.v91 N.v91 R.v92 N.v92 R.v93 N.v93 R.v94 N.v94 R.v95 N.v95 R.v96 N.v96 R.v97 N.v97 R.v98 N.v98 R.v99 N.v99 R.v100 N.v100 R.v101 N.v101 R.v102 N.v102 R.v103 N.v103 R.v104 N.v104 R.v105 N.v105 R.v106 N.v106 R.v107 N.v107 R.v108 N.v108 R.v109 N.v109 R.v110 N.v110 R.v111 N.v111 R.v112 N.v112 R.v113 N.v113 R.v114 N.v114 R.v115 N.v115 R.v116 N.v116 R.v117 N.v117 R.v118 N.v118 R.v119 N.v119 R.v120 N.v120 R.v121 N.v121 R.v122 N.v122 R.v123 N.v123 R.v124 N.v124 R.v125 N.v125 R.v126 N.v126 R.v127 N.v127 R.v128 N.v128 R.v129 N.v129 R.v130 N.v130 R.v131 N.v131 R.v132 N.v132 R.v133 N.v133 R.v134 N.v134 R.v135 N.v135 R.v136 N.v136 R.v137 N.v137 R.v138 N.v138 R.v139 N.v139 R.v140 N.v140 R.v141 N.v141 R.v142 N.v142 R.v143 N.v143 R.v144 N.v144 R.v145 N.v145 R.v146 N.v146 R.v147 N.v147 R.v148 N.v148 R.v149 N.v149 R.v150 N.v150 R.v151 N.v151 R.v152 N.v152 R.v153 N.v153 R.v154 N.v154 R.v155 N.v155 R.v156 N.v156 R.v157 N.v157 R.v158 N.v158 R.v159 N.v159 R.v160 N.v160.
Theorem checks_refine s i : R.assertionChecks (state s) (inputs i) = N.assertionChecks s i.
Proof. unfold R.assertionChecks, N.assertionChecks.
  reflexivity.
Qed.
Theorem asserts_refine s i : N.asserts s i <-> R.asserts (state s) (inputs i).
Proof. unfold N.asserts, R.asserts; rewrite checks_refine; reflexivity. Qed.
Print Assumptions step_refines.
Print Assumptions observe_refines.
Print Assumptions run_refines.
Print Assumptions asserts_refine.
End MulDivRefinement.
