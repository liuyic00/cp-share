(* Generated proof certificates, checked by Rocq. *)
From Stdlib Require Import ZArith Lia List Bool Zmod.Bits.
From BitsGenerated Require Import MulDivChecked.
From ReferenceGenerated Require Import MulDivChecked.
From BitsProofs Require Import Unsigned BitFacts RefinementTactics.
Module MulDivCheckedRefinement.
Module N := BitsGenerated.MulDivChecked.nMulDivChecked.
Module R := ReferenceGenerated.MulDivChecked.nMulDivChecked.
Module NB := BitsGenerated.MulDivChecked.CIRCTBits.
Module RB := ReferenceGenerated.MulDivChecked.CIRCTBits.
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
  (Zmod.unsigned (N.r8_nremainder x))
  (Zmod.unsigned (N.r9_ncontractPending x))
  (Zmod.unsigned (N.r10_ncontractAge x))
  (Zmod.unsigned (N.r11_ncontractFn x))
  (Zmod.unsigned (N.r12_ncontractDw x))
  (Zmod.unsigned (N.r13_ncontractA x))
  (Zmod.unsigned (N.r14_ncontractB x))
  (Zmod.unsigned (N.r15_ncontractTag x))
  (Zmod.unsigned (N.r16_ncontractWasNegated x))
  (Zmod.unsigned (N.r17_ncontractQuotient x))
  (Zmod.unsigned (N.r18_ncontractResidue x))
  (Zmod.unsigned (N.r19_ncontractPreviousData x))
  (Zmod.unsigned (N.r20_ncontractPreviousTag x))
  (Zmod.unsigned (N.r21_ncontractWasStalled x)).
Lemma state_r0_nstate x : R.r0_nstate (state x) = Zmod.unsigned (N.r0_nstate x). Proof. reflexivity. Qed.
Lemma state_r1_nreq_5Fdw x : R.r1_nreq_5Fdw (state x) = Zmod.unsigned (N.r1_nreq_5Fdw x). Proof. reflexivity. Qed.
Lemma state_r2_nreq_5Ftag x : R.r2_nreq_5Ftag (state x) = Zmod.unsigned (N.r2_nreq_5Ftag x). Proof. reflexivity. Qed.
Lemma state_r3_ncount x : R.r3_ncount (state x) = Zmod.unsigned (N.r3_ncount x). Proof. reflexivity. Qed.
Lemma state_r4_nneg_5Fout x : R.r4_nneg_5Fout (state x) = Zmod.unsigned (N.r4_nneg_5Fout x). Proof. reflexivity. Qed.
Lemma state_r5_nisHi x : R.r5_nisHi (state x) = Zmod.unsigned (N.r5_nisHi x). Proof. reflexivity. Qed.
Lemma state_r6_nresHi x : R.r6_nresHi (state x) = Zmod.unsigned (N.r6_nresHi x). Proof. reflexivity. Qed.
Lemma state_r7_ndivisor x : R.r7_ndivisor (state x) = Zmod.unsigned (N.r7_ndivisor x). Proof. reflexivity. Qed.
Lemma state_r8_nremainder x : R.r8_nremainder (state x) = Zmod.unsigned (N.r8_nremainder x). Proof. reflexivity. Qed.
Lemma state_r9_ncontractPending x : R.r9_ncontractPending (state x) = Zmod.unsigned (N.r9_ncontractPending x). Proof. reflexivity. Qed.
Lemma state_r10_ncontractAge x : R.r10_ncontractAge (state x) = Zmod.unsigned (N.r10_ncontractAge x). Proof. reflexivity. Qed.
Lemma state_r11_ncontractFn x : R.r11_ncontractFn (state x) = Zmod.unsigned (N.r11_ncontractFn x). Proof. reflexivity. Qed.
Lemma state_r12_ncontractDw x : R.r12_ncontractDw (state x) = Zmod.unsigned (N.r12_ncontractDw x). Proof. reflexivity. Qed.
Lemma state_r13_ncontractA x : R.r13_ncontractA (state x) = Zmod.unsigned (N.r13_ncontractA x). Proof. reflexivity. Qed.
Lemma state_r14_ncontractB x : R.r14_ncontractB (state x) = Zmod.unsigned (N.r14_ncontractB x). Proof. reflexivity. Qed.
Lemma state_r15_ncontractTag x : R.r15_ncontractTag (state x) = Zmod.unsigned (N.r15_ncontractTag x). Proof. reflexivity. Qed.
Lemma state_r16_ncontractWasNegated x : R.r16_ncontractWasNegated (state x) = Zmod.unsigned (N.r16_ncontractWasNegated x). Proof. reflexivity. Qed.
Lemma state_r17_ncontractQuotient x : R.r17_ncontractQuotient (state x) = Zmod.unsigned (N.r17_ncontractQuotient x). Proof. reflexivity. Qed.
Lemma state_r18_ncontractResidue x : R.r18_ncontractResidue (state x) = Zmod.unsigned (N.r18_ncontractResidue x). Proof. reflexivity. Qed.
Lemma state_r19_ncontractPreviousData x : R.r19_ncontractPreviousData (state x) = Zmod.unsigned (N.r19_ncontractPreviousData x). Proof. reflexivity. Qed.
Lemma state_r20_ncontractPreviousTag x : R.r20_ncontractPreviousTag (state x) = Zmod.unsigned (N.r20_ncontractPreviousTag x). Proof. reflexivity. Qed.
Lemma state_r21_ncontractWasStalled x : R.r21_ncontractWasStalled (state x) = Zmod.unsigned (N.r21_ncontractWasStalled x). Proof. reflexivity. Qed.
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
Lemma repeat_64 (x : bits 1) : RB.repeatWord 64 1 (Zmod.unsigned x) mod 2^64 = Zmod.unsigned (NB.repeatBits 64 64 x).
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
  rewrite !inputs_nio_5Freq_5Fbits_5Ffn.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Freq_5Fbits_5Ffn i)).
  finish_numeric.
Qed.
Lemma node_153 (s : N.State) (i : N.Inputs) : R.v153 (state s) (inputs i) = Zmod.unsigned (N.v153 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v153 s i)) at 1; unfold R.v153, N.v153.
  unfold R.v31, N.v31.
  rewrite ?node_152.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_154 (s : N.State) (i : N.Inputs) : R.v154 (state s) (inputs i) = Zmod.unsigned (N.v154 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v154 s i)) at 1; unfold R.v154, N.v154.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_155 (s : N.State) (i : N.Inputs) : R.v155 (state s) (inputs i) = Zmod.unsigned (N.v155 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v155 s i)) at 1; unfold R.v155, N.v155.
  unfold R.v154, N.v154.
  rewrite !inputs_nio_5Freq_5Fbits_5Ffn.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Freq_5Fbits_5Ffn i)).
  finish_numeric.
Qed.
Lemma node_156 (s : N.State) (i : N.Inputs) : R.v156 (state s) (inputs i) = Zmod.unsigned (N.v156 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v156 s i)) at 1; unfold R.v156, N.v156.
  rewrite !inputs_nio_5Freq_5Fbits_5Ffn.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Freq_5Fbits_5Ffn i)).
  finish_numeric.
Qed.
Lemma node_157 (s : N.State) (i : N.Inputs) : R.v157 (state s) (inputs i) = Zmod.unsigned (N.v157 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v157 s i)) at 1; unfold R.v157, N.v157.
  unfold R.v15, N.v15.
  rewrite ?node_156.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_158 (s : N.State) (i : N.Inputs) : R.v158 (state s) (inputs i) = Zmod.unsigned (N.v158 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v158 s i)) at 1; unfold R.v158, N.v158.
  rewrite ?node_155.
  rewrite ?node_157.
  rewrite !inputs_nio_5Freq_5Fbits_5Fdw.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Freq_5Fbits_5Fdw i)).
  finish_numeric.
Qed.
Lemma node_159 (s : N.State) (i : N.Inputs) : R.v159 (state s) (inputs i) = Zmod.unsigned (N.v159 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v159 s i)) at 1; unfold R.v159, N.v159.
  unfold R.v31, N.v31.
  rewrite !inputs_nio_5Fkill.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fkill i)).
  finish_numeric.
Qed.
Lemma node_160 (s : N.State) (i : N.Inputs) : R.v160 (state s) (inputs i) = Zmod.unsigned (N.v160 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v160 s i)) at 1; unfold R.v160, N.v160.
  rewrite ?node_153.
  rewrite ?node_158.
  rewrite ?node_159.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_161 (s : N.State) (i : N.Inputs) : R.v161 (state s) (inputs i) = Zmod.unsigned (N.v161 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v161 s i)) at 1; unfold R.v161, N.v161.
  unfold R.v31, N.v31.
  rewrite ?node_40.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_162 (s : N.State) (i : N.Inputs) : R.v162 (state s) (inputs i) = Zmod.unsigned (N.v162 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v162 s i)) at 1; unfold R.v162, N.v162.
  rewrite ?node_161.
  rewrite !state_r9_ncontractPending.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r9_ncontractPending s)).
  finish_numeric.
Qed.
Lemma node_163 (s : N.State) (i : N.Inputs) : R.v163 (state s) (inputs i) = Zmod.unsigned (N.v163 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v163 s i)) at 1; unfold R.v163, N.v163.
  rewrite ?node_2.
  rewrite ?node_160.
  rewrite ?node_162.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_164 (s : N.State) (i : N.Inputs) : R.v164 (state s) (inputs i) = Zmod.unsigned (N.v164 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v164 s i)) at 1; unfold R.v164, N.v164.
  unfold R.v31, N.v31.
  rewrite ?node_38.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_165 (s : N.State) (i : N.Inputs) : R.v165 (state s) (inputs i) = Zmod.unsigned (N.v165 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v165 s i)) at 1; unfold R.v165, N.v165.
  rewrite ?node_164.
  rewrite !state_r9_ncontractPending.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r9_ncontractPending s)).
  finish_numeric.
Qed.
Lemma node_166 (s : N.State) (i : N.Inputs) : R.v166 (state s) (inputs i) = Zmod.unsigned (N.v166 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v166 s i)) at 1; unfold R.v166, N.v166.
  unfold R.v68, N.v68.
  rewrite !state_r10_ncontractAge.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r10_ncontractAge s)).
  finish_numeric.
Qed.
Lemma node_167 (s : N.State) (i : N.Inputs) : R.v167 (state s) (inputs i) = Zmod.unsigned (N.v167 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v167 s i)) at 1; unfold R.v167, N.v167.
  rewrite ?node_165.
  rewrite ?node_166.
  rewrite !state_r10_ncontractAge.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r10_ncontractAge s)).
  finish_numeric.
Qed.
Lemma node_168 (s : N.State) (i : N.Inputs) : R.v168 (state s) (inputs i) = Zmod.unsigned (N.v168 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v168 s i)) at 1; unfold R.v168, N.v168.
  rewrite ?node_2.
  unfold R.v82, N.v82.
  rewrite ?node_167.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_169 (s : N.State) (i : N.Inputs) : R.v169 (state s) (inputs i) = Zmod.unsigned (N.v169 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v169 s i)) at 1; unfold R.v169, N.v169.
  rewrite ?node_2.
  rewrite !inputs_nio_5Freq_5Fbits_5Ffn.
  rewrite !state_r11_ncontractFn.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Freq_5Fbits_5Ffn i)).
  rewrite ?(bits.mod_to_Z (N.r11_ncontractFn s)).
  finish_numeric.
Qed.
Lemma node_170 (s : N.State) (i : N.Inputs) : R.v170 (state s) (inputs i) = Zmod.unsigned (N.v170 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v170 s i)) at 1; unfold R.v170, N.v170.
  rewrite ?node_2.
  rewrite !inputs_nio_5Freq_5Fbits_5Fdw.
  rewrite !state_r12_ncontractDw.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Freq_5Fbits_5Fdw i)).
  rewrite ?(bits.mod_to_Z (N.r12_ncontractDw s)).
  finish_numeric.
Qed.
Lemma node_171 (s : N.State) (i : N.Inputs) : R.v171 (state s) (inputs i) = Zmod.unsigned (N.v171 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v171 s i)) at 1; unfold R.v171, N.v171.
  rewrite ?node_2.
  rewrite !inputs_nio_5Freq_5Fbits_5Fin1.
  rewrite !state_r13_ncontractA.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Freq_5Fbits_5Fin1 i)).
  rewrite ?(bits.mod_to_Z (N.r13_ncontractA s)).
  finish_numeric.
Qed.
Lemma node_172 (s : N.State) (i : N.Inputs) : R.v172 (state s) (inputs i) = Zmod.unsigned (N.v172 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v172 s i)) at 1; unfold R.v172, N.v172.
  rewrite ?node_2.
  rewrite !inputs_nio_5Freq_5Fbits_5Fin2.
  rewrite !state_r14_ncontractB.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Freq_5Fbits_5Fin2 i)).
  rewrite ?(bits.mod_to_Z (N.r14_ncontractB s)).
  finish_numeric.
Qed.
Lemma node_173 (s : N.State) (i : N.Inputs) : R.v173 (state s) (inputs i) = Zmod.unsigned (N.v173 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v173 s i)) at 1; unfold R.v173, N.v173.
  rewrite ?node_2.
  rewrite !inputs_nio_5Freq_5Fbits_5Ftag.
  rewrite !state_r15_ncontractTag.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Freq_5Fbits_5Ftag i)).
  rewrite ?(bits.mod_to_Z (N.r15_ncontractTag s)).
  finish_numeric.
Qed.
Lemma node_174 (s : N.State) (i : N.Inputs) : R.v174 (state s) (inputs i) = Zmod.unsigned (N.v174 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v174 s i)) at 1; unfold R.v174, N.v174.
  rewrite ?node_2.
  unfold R.v31, N.v31.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_175 (s : N.State) (i : N.Inputs) : R.v175 (state s) (inputs i) = Zmod.unsigned (N.v175 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v175 s i)) at 1; unfold R.v175, N.v175.
  rewrite ?node_53.
  rewrite !state_r16_ncontractWasNegated.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r16_ncontractWasNegated s)).
  finish_numeric.
Qed.
Lemma node_176 (s : N.State) (i : N.Inputs) : R.v176 (state s) (inputs i) = Zmod.unsigned (N.v176 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v176 s i)) at 1; unfold R.v176, N.v176.
  rewrite ?node_174.
  rewrite ?node_175.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_177 (s : N.State) (i : N.Inputs) : R.v177 (state s) (inputs i) = Zmod.unsigned (N.v177 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v177 s i)) at 1; unfold R.v177, N.v177.
  rewrite ?node_53.
  rewrite ?node_119.
  rewrite !state_r17_ncontractQuotient.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r17_ncontractQuotient s)).
  finish_numeric.
Qed.
Lemma node_178 (s : N.State) (i : N.Inputs) : R.v178 (state s) (inputs i) = Zmod.unsigned (N.v178 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v178 s i)) at 1; unfold R.v178, N.v178.
  rewrite ?node_53.
  rewrite ?node_144.
  rewrite !state_r18_ncontractResidue.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r18_ncontractResidue s)).
  finish_numeric.
Qed.
Lemma node_179 (s : N.State) (i : N.Inputs) : R.v179 (state s) (inputs i) = Zmod.unsigned (N.v179 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v179 s i)) at 1; unfold R.v179, N.v179.
  rewrite ?node_145.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_180 (s : N.State) (i : N.Inputs) : R.v180 (state s) (inputs i) = Zmod.unsigned (N.v180 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v180 s i)) at 1; unfold R.v180, N.v180.
  rewrite !state_r0_nstate.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r0_nstate s)).
  finish_numeric.
Qed.
Lemma node_181 (s : N.State) (i : N.Inputs) : R.v181 (state s) (inputs i) = Zmod.unsigned (N.v181 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v181 s i)) at 1; unfold R.v181, N.v181.
  rewrite ?node_180.
  rewrite !state_r1_nreq_5Fdw.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r1_nreq_5Fdw s)).
  finish_numeric.
Qed.
Lemma node_182 (s : N.State) (i : N.Inputs) : R.v182 (state s) (inputs i) = Zmod.unsigned (N.v182 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v182 s i)) at 1; unfold R.v182, N.v182.
  rewrite ?node_145.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_183 (s : N.State) (i : N.Inputs) : R.v183 (state s) (inputs i) = Zmod.unsigned (N.v183 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v183 s i)) at 1; unfold R.v183, N.v183.
  rewrite ?node_179.
  rewrite ?node_181.
  rewrite ?node_182.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_184 (s : N.State) (i : N.Inputs) : R.v184 (state s) (inputs i) = Zmod.unsigned (N.v184 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v184 s i)) at 1; unfold R.v184, N.v184.
  rewrite ?node_183.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_185 (s : N.State) (i : N.Inputs) : R.v185 (state s) (inputs i) = Zmod.unsigned (N.v185 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v185 s i)) at 1; unfold R.v185, N.v185.
  rewrite ?node_184.
  unfold RB.word.
  rewrite repeat_32, bits.mod_to_Z; reflexivity.
Qed.
Lemma node_186 (s : N.State) (i : N.Inputs) : R.v186 (state s) (inputs i) = Zmod.unsigned (N.v186 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v186 s i)) at 1; unfold R.v186, N.v186.
  rewrite ?node_179.
  rewrite ?node_185.
  rewrite !state_r1_nreq_5Fdw.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r1_nreq_5Fdw s)).
  finish_numeric.
Qed.
Lemma node_187 (s : N.State) (i : N.Inputs) : R.v187 (state s) (inputs i) = Zmod.unsigned (N.v187 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v187 s i)) at 1; unfold R.v187, N.v187.
  rewrite ?node_183.
  rewrite ?node_186.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_188 (s : N.State) (i : N.Inputs) : R.v188 (state s) (inputs i) = Zmod.unsigned (N.v188 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v188 s i)) at 1; unfold R.v188, N.v188.
  unfold R.v31, N.v31.
  rewrite !inputs_nio_5Fresp_5Fready.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fresp_5Fready i)).
  finish_numeric.
Qed.
Lemma node_189 (s : N.State) (i : N.Inputs) : R.v189 (state s) (inputs i) = Zmod.unsigned (N.v189 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v189 s i)) at 1; unfold R.v189, N.v189.
  unfold R.v31, N.v31.
  rewrite !inputs_nio_5Fkill.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fkill i)).
  finish_numeric.
Qed.
Lemma node_190 (s : N.State) (i : N.Inputs) : R.v190 (state s) (inputs i) = Zmod.unsigned (N.v190 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v190 s i)) at 1; unfold R.v190, N.v190.
  rewrite ?node_38.
  rewrite ?node_188.
  rewrite ?node_189.
  rewrite !state_r9_ncontractPending.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r9_ncontractPending s)).
  finish_numeric.
Qed.
Lemma node_191 (s : N.State) (i : N.Inputs) : R.v191 (state s) (inputs i) = Zmod.unsigned (N.v191 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v191 s i)) at 1; unfold R.v191, N.v191.
  rewrite !state_r11_ncontractFn.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r11_ncontractFn s)).
  finish_numeric.
Qed.
Lemma node_192 (s : N.State) (i : N.Inputs) : R.v192 (state s) (inputs i) = Zmod.unsigned (N.v192 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v192 s i)) at 1; unfold R.v192, N.v192.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_193 (s : N.State) (i : N.Inputs) : R.v193 (state s) (inputs i) = Zmod.unsigned (N.v193 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v193 s i)) at 1; unfold R.v193, N.v193.
  rewrite !state_r11_ncontractFn.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r11_ncontractFn s)).
  finish_numeric.
Qed.
Lemma node_194 (s : N.State) (i : N.Inputs) : R.v194 (state s) (inputs i) = Zmod.unsigned (N.v194 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v194 s i)) at 1; unfold R.v194, N.v194.
  unfold R.v31, N.v31.
  rewrite ?node_193.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_195 (s : N.State) (i : N.Inputs) : R.v195 (state s) (inputs i) = Zmod.unsigned (N.v195 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v195 s i)) at 1; unfold R.v195, N.v195.
  rewrite !state_r13_ncontractA.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r13_ncontractA s)).
  finish_numeric.
Qed.
Lemma node_196 (s : N.State) (i : N.Inputs) : R.v196 (state s) (inputs i) = Zmod.unsigned (N.v196 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v196 s i)) at 1; unfold R.v196, N.v196.
  rewrite ?node_194.
  rewrite ?node_195.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_197 (s : N.State) (i : N.Inputs) : R.v197 (state s) (inputs i) = Zmod.unsigned (N.v197 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v197 s i)) at 1; unfold R.v197, N.v197.
  rewrite ?node_196.
  unfold RB.word.
  rewrite repeat_32, bits.mod_to_Z; reflexivity.
Qed.
Lemma node_198 (s : N.State) (i : N.Inputs) : R.v198 (state s) (inputs i) = Zmod.unsigned (N.v198 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v198 s i)) at 1; unfold R.v198, N.v198.
  rewrite !state_r13_ncontractA.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r13_ncontractA s)).
  finish_numeric.
Qed.
Lemma node_199 (s : N.State) (i : N.Inputs) : R.v199 (state s) (inputs i) = Zmod.unsigned (N.v199 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v199 s i)) at 1; unfold R.v199, N.v199.
  rewrite ?node_197.
  rewrite ?node_198.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_200 (s : N.State) (i : N.Inputs) : R.v200 (state s) (inputs i) = Zmod.unsigned (N.v200 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v200 s i)) at 1; unfold R.v200, N.v200.
  rewrite ?node_199.
  rewrite !state_r12_ncontractDw.
  rewrite !state_r13_ncontractA.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r12_ncontractDw s)).
  rewrite ?(bits.mod_to_Z (N.r13_ncontractA s)).
  finish_numeric.
Qed.
Lemma node_201 (s : N.State) (i : N.Inputs) : R.v201 (state s) (inputs i) = Zmod.unsigned (N.v201 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v201 s i)) at 1; unfold R.v201, N.v201.
  rewrite ?node_200.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_202 (s : N.State) (i : N.Inputs) : R.v202 (state s) (inputs i) = Zmod.unsigned (N.v202 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v202 s i)) at 1; unfold R.v202, N.v202.
  rewrite ?node_194.
  rewrite ?node_201.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_203 (s : N.State) (i : N.Inputs) : R.v203 (state s) (inputs i) = Zmod.unsigned (N.v203 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v203 s i)) at 1; unfold R.v203, N.v203.
  rewrite !state_r14_ncontractB.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r14_ncontractB s)).
  finish_numeric.
Qed.
Lemma node_204 (s : N.State) (i : N.Inputs) : R.v204 (state s) (inputs i) = Zmod.unsigned (N.v204 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v204 s i)) at 1; unfold R.v204, N.v204.
  rewrite ?node_194.
  rewrite ?node_203.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_205 (s : N.State) (i : N.Inputs) : R.v205 (state s) (inputs i) = Zmod.unsigned (N.v205 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v205 s i)) at 1; unfold R.v205, N.v205.
  rewrite ?node_204.
  unfold RB.word.
  rewrite repeat_32, bits.mod_to_Z; reflexivity.
Qed.
Lemma node_206 (s : N.State) (i : N.Inputs) : R.v206 (state s) (inputs i) = Zmod.unsigned (N.v206 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v206 s i)) at 1; unfold R.v206, N.v206.
  rewrite !state_r14_ncontractB.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r14_ncontractB s)).
  finish_numeric.
Qed.
Lemma node_207 (s : N.State) (i : N.Inputs) : R.v207 (state s) (inputs i) = Zmod.unsigned (N.v207 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v207 s i)) at 1; unfold R.v207, N.v207.
  rewrite ?node_205.
  rewrite ?node_206.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_208 (s : N.State) (i : N.Inputs) : R.v208 (state s) (inputs i) = Zmod.unsigned (N.v208 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v208 s i)) at 1; unfold R.v208, N.v208.
  rewrite ?node_207.
  rewrite !state_r12_ncontractDw.
  rewrite !state_r14_ncontractB.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r12_ncontractDw s)).
  rewrite ?(bits.mod_to_Z (N.r14_ncontractB s)).
  finish_numeric.
Qed.
Lemma node_209 (s : N.State) (i : N.Inputs) : R.v209 (state s) (inputs i) = Zmod.unsigned (N.v209 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v209 s i)) at 1; unfold R.v209, N.v209.
  rewrite ?node_208.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_210 (s : N.State) (i : N.Inputs) : R.v210 (state s) (inputs i) = Zmod.unsigned (N.v210 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v210 s i)) at 1; unfold R.v210, N.v210.
  rewrite ?node_194.
  rewrite ?node_209.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_211 (s : N.State) (i : N.Inputs) : R.v211 (state s) (inputs i) = Zmod.unsigned (N.v211 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v211 s i)) at 1; unfold R.v211, N.v211.
  rewrite ?node_202.
  rewrite ?node_210.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_212 (s : N.State) (i : N.Inputs) : R.v212 (state s) (inputs i) = Zmod.unsigned (N.v212 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v212 s i)) at 1; unfold R.v212, N.v212.
  unfold R.v192, N.v192.
  rewrite ?node_211.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_213 (s : N.State) (i : N.Inputs) : R.v213 (state s) (inputs i) = Zmod.unsigned (N.v213 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v213 s i)) at 1; unfold R.v213, N.v213.
  rewrite !state_r11_ncontractFn.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r11_ncontractFn s)).
  finish_numeric.
Qed.
Lemma node_214 (s : N.State) (i : N.Inputs) : R.v214 (state s) (inputs i) = Zmod.unsigned (N.v214 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v214 s i)) at 1; unfold R.v214, N.v214.
  rewrite ?node_202.
  rewrite ?node_210.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_215 (s : N.State) (i : N.Inputs) : R.v215 (state s) (inputs i) = Zmod.unsigned (N.v215 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v215 s i)) at 1; unfold R.v215, N.v215.
  unfold R.v143, N.v143.
  rewrite ?node_208.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_216 (s : N.State) (i : N.Inputs) : R.v216 (state s) (inputs i) = Zmod.unsigned (N.v216 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v216 s i)) at 1; unfold R.v216, N.v216.
  rewrite ?node_208.
  rewrite ?node_210.
  rewrite ?node_215.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_217 (s : N.State) (i : N.Inputs) : R.v217 (state s) (inputs i) = Zmod.unsigned (N.v217 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v217 s i)) at 1; unfold R.v217, N.v217.
  unfold R.v143, N.v143.
  rewrite ?node_216.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_218 (s : N.State) (i : N.Inputs) : R.v218 (state s) (inputs i) = Zmod.unsigned (N.v218 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v218 s i)) at 1; unfold R.v218, N.v218.
  rewrite ?node_214.
  rewrite ?node_217.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_219 (s : N.State) (i : N.Inputs) : R.v219 (state s) (inputs i) = Zmod.unsigned (N.v219 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v219 s i)) at 1; unfold R.v219, N.v219.
  rewrite ?node_202.
  rewrite ?node_213.
  rewrite ?node_218.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_220 (s : N.State) (i : N.Inputs) : R.v220 (state s) (inputs i) = Zmod.unsigned (N.v220 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v220 s i)) at 1; unfold R.v220, N.v220.
  unfold R.v192, N.v192.
  rewrite ?node_219.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_221 (s : N.State) (i : N.Inputs) : R.v221 (state s) (inputs i) = Zmod.unsigned (N.v221 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v221 s i)) at 1; unfold R.v221, N.v221.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_222 (s : N.State) (i : N.Inputs) : R.v222 (state s) (inputs i) = Zmod.unsigned (N.v222 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v222 s i)) at 1; unfold R.v222, N.v222.
  rewrite ?node_212.
  rewrite ?node_220.
  unfold R.v221, N.v221.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_223 (s : N.State) (i : N.Inputs) : R.v223 (state s) (inputs i) = Zmod.unsigned (N.v223 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v223 s i)) at 1; unfold R.v223, N.v223.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_224 (s : N.State) (i : N.Inputs) : R.v224 (state s) (inputs i) = Zmod.unsigned (N.v224 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v224 s i)) at 1; unfold R.v224, N.v224.
  unfold R.v43, N.v43.
  unfold R.v223, N.v223.
  rewrite !state_r12_ncontractDw.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r12_ncontractDw s)).
  finish_numeric.
Qed.
Lemma node_225 (s : N.State) (i : N.Inputs) : R.v225 (state s) (inputs i) = Zmod.unsigned (N.v225 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v225 s i)) at 1; unfold R.v225, N.v225.
  rewrite ?node_191.
  rewrite ?node_222.
  rewrite ?node_224.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_226 (s : N.State) (i : N.Inputs) : R.v226 (state s) (inputs i) = Zmod.unsigned (N.v226 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v226 s i)) at 1; unfold R.v226, N.v226.
  rewrite ?node_225.
  rewrite !state_r10_ncontractAge.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r10_ncontractAge s)).
  finish_numeric.
Qed.
Lemma node_227 (s : N.State) (i : N.Inputs) : R.v227 (state s) (inputs i) = Zmod.unsigned (N.v227 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v227 s i)) at 1; unfold R.v227, N.v227.
  rewrite ?node_189.
  rewrite !state_r9_ncontractPending.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r9_ncontractPending s)).
  finish_numeric.
Qed.
Lemma node_228 (s : N.State) (i : N.Inputs) : R.v228 (state s) (inputs i) = Zmod.unsigned (N.v228 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v228 s i)) at 1; unfold R.v228, N.v228.
  unfold R.v31, N.v31.
  rewrite !inputs_nreset.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  finish_numeric.
Qed.
Lemma node_229 (s : N.State) (i : N.Inputs) : R.v229 (state s) (inputs i) = Zmod.unsigned (N.v229 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v229 s i)) at 1; unfold R.v229, N.v229.
  rewrite ?node_227.
  rewrite ?node_228.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_230 (s : N.State) (i : N.Inputs) : R.v230 (state s) (inputs i) = Zmod.unsigned (N.v230 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v230 s i)) at 1; unfold R.v230, N.v230.
  rewrite ?node_225.
  rewrite !state_r10_ncontractAge.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r10_ncontractAge s)).
  finish_numeric.
Qed.
Lemma node_231 (s : N.State) (i : N.Inputs) : R.v231 (state s) (inputs i) = Zmod.unsigned (N.v231 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v231 s i)) at 1; unfold R.v231, N.v231.
  rewrite ?node_38.
  rewrite ?node_230.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_232 (s : N.State) (i : N.Inputs) : R.v232 (state s) (inputs i) = Zmod.unsigned (N.v232 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v232 s i)) at 1; unfold R.v232, N.v232.
  rewrite !state_r15_ncontractTag.
  rewrite !state_r2_nreq_5Ftag.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r15_ncontractTag s)).
  rewrite ?(bits.mod_to_Z (N.r2_nreq_5Ftag s)).
  finish_numeric.
Qed.
Lemma node_233 (s : N.State) (i : N.Inputs) : R.v233 (state s) (inputs i) = Zmod.unsigned (N.v233 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v233 s i)) at 1; unfold R.v233, N.v233.
  rewrite ?node_38.
  rewrite ?node_227.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_234 (s : N.State) (i : N.Inputs) : R.v234 (state s) (inputs i) = Zmod.unsigned (N.v234 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v234 s i)) at 1; unfold R.v234, N.v234.
  rewrite ?node_228.
  rewrite ?node_233.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_235 (s : N.State) (i : N.Inputs) : R.v235 (state s) (inputs i) = Zmod.unsigned (N.v235 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v235 s i)) at 1; unfold R.v235, N.v235.
  rewrite ?node_144.
  rewrite !state_r16_ncontractWasNegated.
  rewrite !state_r18_ncontractResidue.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r16_ncontractWasNegated s)).
  rewrite ?(bits.mod_to_Z (N.r18_ncontractResidue s)).
  finish_numeric.
Qed.
Lemma node_236 (s : N.State) (i : N.Inputs) : R.v236 (state s) (inputs i) = Zmod.unsigned (N.v236 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v236 s i)) at 1; unfold R.v236, N.v236.
  rewrite ?node_119.
  rewrite !state_r16_ncontractWasNegated.
  rewrite !state_r17_ncontractQuotient.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r16_ncontractWasNegated s)).
  rewrite ?(bits.mod_to_Z (N.r17_ncontractQuotient s)).
  finish_numeric.
Qed.
Lemma node_237 (s : N.State) (i : N.Inputs) : R.v237 (state s) (inputs i) = Zmod.unsigned (N.v237 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v237 s i)) at 1; unfold R.v237, N.v237.
  rewrite ?node_213.
  rewrite ?node_235.
  rewrite ?node_236.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_238 (s : N.State) (i : N.Inputs) : R.v238 (state s) (inputs i) = Zmod.unsigned (N.v238 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v238 s i)) at 1; unfold R.v238, N.v238.
  unfold R.v143, N.v143.
  rewrite ?node_237.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_239 (s : N.State) (i : N.Inputs) : R.v239 (state s) (inputs i) = Zmod.unsigned (N.v239 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v239 s i)) at 1; unfold R.v239, N.v239.
  rewrite ?node_219.
  rewrite ?node_237.
  rewrite ?node_238.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_240 (s : N.State) (i : N.Inputs) : R.v240 (state s) (inputs i) = Zmod.unsigned (N.v240 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v240 s i)) at 1; unfold R.v240, N.v240.
  unfold R.v154, N.v154.
  rewrite !state_r11_ncontractFn.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r11_ncontractFn s)).
  finish_numeric.
Qed.
Lemma node_241 (s : N.State) (i : N.Inputs) : R.v241 (state s) (inputs i) = Zmod.unsigned (N.v241 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v241 s i)) at 1; unfold R.v241, N.v241.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_242 (s : N.State) (i : N.Inputs) : R.v242 (state s) (inputs i) = Zmod.unsigned (N.v242 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v242 s i)) at 1; unfold R.v242, N.v242.
  unfold R.v241, N.v241.
  rewrite !state_r11_ncontractFn.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r11_ncontractFn s)).
  finish_numeric.
Qed.
Lemma node_243 (s : N.State) (i : N.Inputs) : R.v243 (state s) (inputs i) = Zmod.unsigned (N.v243 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v243 s i)) at 1; unfold R.v243, N.v243.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_244 (s : N.State) (i : N.Inputs) : R.v244 (state s) (inputs i) = Zmod.unsigned (N.v244 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v244 s i)) at 1; unfold R.v244, N.v244.
  unfold R.v243, N.v243.
  rewrite !state_r11_ncontractFn.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r11_ncontractFn s)).
  finish_numeric.
Qed.
Lemma node_245 (s : N.State) (i : N.Inputs) : R.v245 (state s) (inputs i) = Zmod.unsigned (N.v245 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v245 s i)) at 1; unfold R.v245, N.v245.
  rewrite ?node_242.
  rewrite ?node_244.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_246 (s : N.State) (i : N.Inputs) : R.v246 (state s) (inputs i) = Zmod.unsigned (N.v246 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v246 s i)) at 1; unfold R.v246, N.v246.
  rewrite !state_r13_ncontractA.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r13_ncontractA s)).
  finish_numeric.
Qed.
Lemma node_247 (s : N.State) (i : N.Inputs) : R.v247 (state s) (inputs i) = Zmod.unsigned (N.v247 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v247 s i)) at 1; unfold R.v247, N.v247.
  rewrite ?node_245.
  rewrite ?node_246.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_248 (s : N.State) (i : N.Inputs) : R.v248 (state s) (inputs i) = Zmod.unsigned (N.v248 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v248 s i)) at 1; unfold R.v248, N.v248.
  rewrite ?node_247.
  unfold RB.word.
  rewrite repeat_64, bits.mod_to_Z; reflexivity.
Qed.
Lemma node_249 (s : N.State) (i : N.Inputs) : R.v249 (state s) (inputs i) = Zmod.unsigned (N.v249 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v249 s i)) at 1; unfold R.v249, N.v249.
  rewrite ?node_248.
  rewrite !state_r13_ncontractA.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r13_ncontractA s)).
  finish_numeric.
Qed.
Lemma node_250 (s : N.State) (i : N.Inputs) : R.v250 (state s) (inputs i) = Zmod.unsigned (N.v250 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v250 s i)) at 1; unfold R.v250, N.v250.
  rewrite !state_r14_ncontractB.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r14_ncontractB s)).
  finish_numeric.
Qed.
Lemma node_251 (s : N.State) (i : N.Inputs) : R.v251 (state s) (inputs i) = Zmod.unsigned (N.v251 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v251 s i)) at 1; unfold R.v251, N.v251.
  rewrite ?node_242.
  rewrite ?node_250.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_252 (s : N.State) (i : N.Inputs) : R.v252 (state s) (inputs i) = Zmod.unsigned (N.v252 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v252 s i)) at 1; unfold R.v252, N.v252.
  rewrite ?node_251.
  unfold RB.word.
  rewrite repeat_64, bits.mod_to_Z; reflexivity.
Qed.
Lemma node_253 (s : N.State) (i : N.Inputs) : R.v253 (state s) (inputs i) = Zmod.unsigned (N.v253 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v253 s i)) at 1; unfold R.v253, N.v253.
  rewrite ?node_252.
  rewrite !state_r14_ncontractB.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r14_ncontractB s)).
  finish_numeric.
Qed.
Lemma node_254 (s : N.State) (i : N.Inputs) : R.v254 (state s) (inputs i) = Zmod.unsigned (N.v254 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v254 s i)) at 1; unfold R.v254, N.v254.
  rewrite ?node_249.
  rewrite ?node_253.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_255 (s : N.State) (i : N.Inputs) : R.v255 (state s) (inputs i) = Zmod.unsigned (N.v255 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v255 s i)) at 1; unfold R.v255, N.v255.
  rewrite ?node_254.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_256 (s : N.State) (i : N.Inputs) : R.v256 (state s) (inputs i) = Zmod.unsigned (N.v256 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v256 s i)) at 1; unfold R.v256, N.v256.
  rewrite ?node_254.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_257 (s : N.State) (i : N.Inputs) : R.v257 (state s) (inputs i) = Zmod.unsigned (N.v257 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v257 s i)) at 1; unfold R.v257, N.v257.
  rewrite ?node_240.
  rewrite ?node_255.
  rewrite ?node_256.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_258 (s : N.State) (i : N.Inputs) : R.v258 (state s) (inputs i) = Zmod.unsigned (N.v258 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v258 s i)) at 1; unfold R.v258, N.v258.
  rewrite ?node_191.
  rewrite ?node_239.
  rewrite ?node_257.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_259 (s : N.State) (i : N.Inputs) : R.v259 (state s) (inputs i) = Zmod.unsigned (N.v259 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v259 s i)) at 1; unfold R.v259, N.v259.
  rewrite ?node_258.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_260 (s : N.State) (i : N.Inputs) : R.v260 (state s) (inputs i) = Zmod.unsigned (N.v260 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v260 s i)) at 1; unfold R.v260, N.v260.
  rewrite ?node_259.
  unfold RB.word.
  rewrite repeat_32, bits.mod_to_Z; reflexivity.
Qed.
Lemma node_261 (s : N.State) (i : N.Inputs) : R.v261 (state s) (inputs i) = Zmod.unsigned (N.v261 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v261 s i)) at 1; unfold R.v261, N.v261.
  rewrite ?node_258.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_262 (s : N.State) (i : N.Inputs) : R.v262 (state s) (inputs i) = Zmod.unsigned (N.v262 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v262 s i)) at 1; unfold R.v262, N.v262.
  rewrite ?node_260.
  rewrite ?node_261.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_263 (s : N.State) (i : N.Inputs) : R.v263 (state s) (inputs i) = Zmod.unsigned (N.v263 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v263 s i)) at 1; unfold R.v263, N.v263.
  rewrite ?node_258.
  rewrite ?node_262.
  rewrite !state_r12_ncontractDw.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r12_ncontractDw s)).
  finish_numeric.
Qed.
Lemma node_264 (s : N.State) (i : N.Inputs) : R.v264 (state s) (inputs i) = Zmod.unsigned (N.v264 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v264 s i)) at 1; unfold R.v264, N.v264.
  rewrite ?node_187.
  rewrite ?node_263.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_265 (s : N.State) (i : N.Inputs) : R.v265 (state s) (inputs i) = Zmod.unsigned (N.v265 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v265 s i)) at 1; unfold R.v265, N.v265.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_266 (s : N.State) (i : N.Inputs) : R.v266 (state s) (inputs i) = Zmod.unsigned (N.v266 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v266 s i)) at 1; unfold R.v266, N.v266.
  rewrite ?node_236.
  unfold R.v265, N.v265.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_267 (s : N.State) (i : N.Inputs) : R.v267 (state s) (inputs i) = Zmod.unsigned (N.v267 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v267 s i)) at 1; unfold R.v267, N.v267.
  rewrite ?node_191.
  rewrite ?node_233.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_268 (s : N.State) (i : N.Inputs) : R.v268 (state s) (inputs i) = Zmod.unsigned (N.v268 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v268 s i)) at 1; unfold R.v268, N.v268.
  unfold R.v143, N.v143.
  rewrite ?node_216.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_269 (s : N.State) (i : N.Inputs) : R.v269 (state s) (inputs i) = Zmod.unsigned (N.v269 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v269 s i)) at 1; unfold R.v269, N.v269.
  unfold R.v31, N.v31.
  rewrite ?node_268.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_270 (s : N.State) (i : N.Inputs) : R.v270 (state s) (inputs i) = Zmod.unsigned (N.v270 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v270 s i)) at 1; unfold R.v270, N.v270.
  rewrite ?node_228.
  rewrite ?node_267.
  rewrite ?node_269.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_271 (s : N.State) (i : N.Inputs) : R.v271 (state s) (inputs i) = Zmod.unsigned (N.v271 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v271 s i)) at 1; unfold R.v271, N.v271.
  unfold R.v143, N.v143.
  rewrite ?node_200.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_272 (s : N.State) (i : N.Inputs) : R.v272 (state s) (inputs i) = Zmod.unsigned (N.v272 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v272 s i)) at 1; unfold R.v272, N.v272.
  rewrite ?node_200.
  rewrite ?node_202.
  rewrite ?node_271.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_273 (s : N.State) (i : N.Inputs) : R.v273 (state s) (inputs i) = Zmod.unsigned (N.v273 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v273 s i)) at 1; unfold R.v273, N.v273.
  rewrite ?node_235.
  rewrite ?node_272.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_274 (s : N.State) (i : N.Inputs) : R.v274 (state s) (inputs i) = Zmod.unsigned (N.v274 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v274 s i)) at 1; unfold R.v274, N.v274.
  unfold R.v143, N.v143.
  rewrite ?node_236.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_275 (s : N.State) (i : N.Inputs) : R.v275 (state s) (inputs i) = Zmod.unsigned (N.v275 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v275 s i)) at 1; unfold R.v275, N.v275.
  unfold R.v143, N.v143.
  rewrite ?node_216.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_276 (s : N.State) (i : N.Inputs) : R.v276 (state s) (inputs i) = Zmod.unsigned (N.v276 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v276 s i)) at 1; unfold R.v276, N.v276.
  rewrite ?node_274.
  rewrite ?node_275.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_277 (s : N.State) (i : N.Inputs) : R.v277 (state s) (inputs i) = Zmod.unsigned (N.v277 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v277 s i)) at 1; unfold R.v277, N.v277.
  unfold R.v8, N.v8.
  rewrite ?node_276.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_278 (s : N.State) (i : N.Inputs) : R.v278 (state s) (inputs i) = Zmod.unsigned (N.v278 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v278 s i)) at 1; unfold R.v278, N.v278.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_279 (s : N.State) (i : N.Inputs) : R.v279 (state s) (inputs i) = Zmod.unsigned (N.v279 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v279 s i)) at 1; unfold R.v279, N.v279.
  rewrite ?node_235.
  unfold R.v278, N.v278.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_280 (s : N.State) (i : N.Inputs) : R.v280 (state s) (inputs i) = Zmod.unsigned (N.v280 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v280 s i)) at 1; unfold R.v280, N.v280.
  rewrite ?node_277.
  rewrite ?node_279.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_281 (s : N.State) (i : N.Inputs) : R.v281 (state s) (inputs i) = Zmod.unsigned (N.v281 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v281 s i)) at 1; unfold R.v281, N.v281.
  rewrite ?node_272.
  unfold R.v278, N.v278.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_282 (s : N.State) (i : N.Inputs) : R.v282 (state s) (inputs i) = Zmod.unsigned (N.v282 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v282 s i)) at 1; unfold R.v282, N.v282.
  rewrite ?node_280.
  rewrite ?node_281.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_283 (s : N.State) (i : N.Inputs) : R.v283 (state s) (inputs i) = Zmod.unsigned (N.v283 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v283 s i)) at 1; unfold R.v283, N.v283.
  rewrite ?node_228.
  rewrite ?node_267.
  rewrite ?node_268.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_284 (s : N.State) (i : N.Inputs) : R.v284 (state s) (inputs i) = Zmod.unsigned (N.v284 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v284 s i)) at 1; unfold R.v284, N.v284.
  rewrite ?node_216.
  rewrite ?node_235.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_285 (s : N.State) (i : N.Inputs) : R.v285 (state s) (inputs i) = Zmod.unsigned (N.v285 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v285 s i)) at 1; unfold R.v285, N.v285.
  rewrite ?node_189.
  rewrite ?node_228.
  rewrite !state_r21_ncontractWasStalled.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r21_ncontractWasStalled s)).
  finish_numeric.
Qed.
Lemma node_286 (s : N.State) (i : N.Inputs) : R.v286 (state s) (inputs i) = Zmod.unsigned (N.v286 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v286 s i)) at 1; unfold R.v286, N.v286.
  rewrite ?node_187.
  rewrite !state_r19_ncontractPreviousData.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r19_ncontractPreviousData s)).
  finish_numeric.
Qed.
Lemma node_287 (s : N.State) (i : N.Inputs) : R.v287 (state s) (inputs i) = Zmod.unsigned (N.v287 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v287 s i)) at 1; unfold R.v287, N.v287.
  rewrite !state_r20_ncontractPreviousTag.
  rewrite !state_r2_nreq_5Ftag.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r20_ncontractPreviousTag s)).
  rewrite ?(bits.mod_to_Z (N.r2_nreq_5Ftag s)).
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
  R.r9_ncontractPending a = R.r9_ncontractPending b ->
  R.r10_ncontractAge a = R.r10_ncontractAge b ->
  R.r11_ncontractFn a = R.r11_ncontractFn b ->
  R.r12_ncontractDw a = R.r12_ncontractDw b ->
  R.r13_ncontractA a = R.r13_ncontractA b ->
  R.r14_ncontractB a = R.r14_ncontractB b ->
  R.r15_ncontractTag a = R.r15_ncontractTag b ->
  R.r16_ncontractWasNegated a = R.r16_ncontractWasNegated b ->
  R.r17_ncontractQuotient a = R.r17_ncontractQuotient b ->
  R.r18_ncontractResidue a = R.r18_ncontractResidue b ->
  R.r19_ncontractPreviousData a = R.r19_ncontractPreviousData b ->
  R.r20_ncontractPreviousTag a = R.r20_ncontractPreviousTag b ->
  R.r21_ncontractWasStalled a = R.r21_ncontractWasStalled b ->
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
  - rewrite state_r9_ncontractPending.
    change (Zmod.unsigned (if Zmod.eqb (N.nreset i) Zmod.one then N.v8 s i else N.v163 s i) =
      if Z.eqb (Zmod.unsigned (N.nreset i) mod 2^1) 1 then R.v8 (state s) (inputs i) else R.v163 (state s) (inputs i)).
    rewrite bits.mod_to_Z, node_8, node_163; finish_numeric.
  - rewrite state_r10_ncontractAge.
    change (Zmod.unsigned (if Zmod.eqb (N.nreset i) Zmod.one then N.v82 s i else N.v168 s i) =
      if Z.eqb (Zmod.unsigned (N.nreset i) mod 2^1) 1 then R.v82 (state s) (inputs i) else R.v168 (state s) (inputs i)).
    rewrite bits.mod_to_Z, node_82, node_168; finish_numeric.
  - rewrite state_r11_ncontractFn.
    change (Zmod.unsigned (N.v169 s i) = R.v169 (state s) (inputs i)); symmetry; exact (node_169 s i).
  - rewrite state_r12_ncontractDw.
    change (Zmod.unsigned (N.v170 s i) = R.v170 (state s) (inputs i)); symmetry; exact (node_170 s i).
  - rewrite state_r13_ncontractA.
    change (Zmod.unsigned (N.v171 s i) = R.v171 (state s) (inputs i)); symmetry; exact (node_171 s i).
  - rewrite state_r14_ncontractB.
    change (Zmod.unsigned (N.v172 s i) = R.v172 (state s) (inputs i)); symmetry; exact (node_172 s i).
  - rewrite state_r15_ncontractTag.
    change (Zmod.unsigned (N.v173 s i) = R.v173 (state s) (inputs i)); symmetry; exact (node_173 s i).
  - rewrite state_r16_ncontractWasNegated.
    change (Zmod.unsigned (if Zmod.eqb (N.nreset i) Zmod.one then N.v8 s i else N.v176 s i) =
      if Z.eqb (Zmod.unsigned (N.nreset i) mod 2^1) 1 then R.v8 (state s) (inputs i) else R.v176 (state s) (inputs i)).
    rewrite bits.mod_to_Z, node_8, node_176; finish_numeric.
  - rewrite state_r17_ncontractQuotient.
    change (Zmod.unsigned (N.v177 s i) = R.v177 (state s) (inputs i)); symmetry; exact (node_177 s i).
  - rewrite state_r18_ncontractResidue.
    change (Zmod.unsigned (N.v178 s i) = R.v178 (state s) (inputs i)); symmetry; exact (node_178 s i).
  - rewrite state_r19_ncontractPreviousData.
    change (Zmod.unsigned (N.v187 s i) = R.v187 (state s) (inputs i)); symmetry; exact (node_187 s i).
  - rewrite state_r20_ncontractPreviousTag.
    change (Zmod.unsigned (N.r2_nreq_5Ftag s) = RB.word 5 (R.r2_nreq_5Ftag (state s))).
    rewrite state_r2_nreq_5Ftag; unfold RB.word; symmetry; apply bits.mod_to_Z.
  - rewrite state_r21_ncontractWasStalled.
    change (Zmod.unsigned (if Zmod.eqb (N.nreset i) Zmod.one then N.v8 s i else N.v190 s i) =
      if Z.eqb (Zmod.unsigned (N.nreset i) mod 2^1) 1 then R.v8 (state s) (inputs i) else R.v190 (state s) (inputs i)).
    rewrite bits.mod_to_Z, node_8, node_190; finish_numeric.
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
  exact (node_187 s i).
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
Local Opaque R.v0 N.v0 R.v1 N.v1 R.v2 N.v2 R.v3 N.v3 R.v4 N.v4 R.v5 N.v5 R.v6 N.v6 R.v7 N.v7 R.v8 N.v8 R.v9 N.v9 R.v10 N.v10 R.v11 N.v11 R.v12 N.v12 R.v13 N.v13 R.v14 N.v14 R.v15 N.v15 R.v16 N.v16 R.v17 N.v17 R.v18 N.v18 R.v19 N.v19 R.v20 N.v20 R.v21 N.v21 R.v22 N.v22 R.v23 N.v23 R.v24 N.v24 R.v25 N.v25 R.v26 N.v26 R.v27 N.v27 R.v28 N.v28 R.v29 N.v29 R.v30 N.v30 R.v31 N.v31 R.v32 N.v32 R.v33 N.v33 R.v34 N.v34 R.v35 N.v35 R.v36 N.v36 R.v37 N.v37 R.v38 N.v38 R.v39 N.v39 R.v40 N.v40 R.v41 N.v41 R.v42 N.v42 R.v43 N.v43 R.v44 N.v44 R.v45 N.v45 R.v46 N.v46 R.v47 N.v47 R.v48 N.v48 R.v49 N.v49 R.v50 N.v50 R.v51 N.v51 R.v52 N.v52 R.v53 N.v53 R.v54 N.v54 R.v55 N.v55 R.v56 N.v56 R.v57 N.v57 R.v58 N.v58 R.v59 N.v59 R.v60 N.v60 R.v61 N.v61 R.v62 N.v62 R.v63 N.v63 R.v64 N.v64 R.v65 N.v65 R.v66 N.v66 R.v67 N.v67 R.v68 N.v68 R.v69 N.v69 R.v70 N.v70 R.v71 N.v71 R.v72 N.v72 R.v73 N.v73 R.v74 N.v74 R.v75 N.v75 R.v76 N.v76 R.v77 N.v77 R.v78 N.v78 R.v79 N.v79 R.v80 N.v80 R.v81 N.v81 R.v82 N.v82 R.v83 N.v83 R.v84 N.v84 R.v85 N.v85 R.v86 N.v86 R.v87 N.v87 R.v88 N.v88 R.v89 N.v89 R.v90 N.v90 R.v91 N.v91 R.v92 N.v92 R.v93 N.v93 R.v94 N.v94 R.v95 N.v95 R.v96 N.v96 R.v97 N.v97 R.v98 N.v98 R.v99 N.v99 R.v100 N.v100 R.v101 N.v101 R.v102 N.v102 R.v103 N.v103 R.v104 N.v104 R.v105 N.v105 R.v106 N.v106 R.v107 N.v107 R.v108 N.v108 R.v109 N.v109 R.v110 N.v110 R.v111 N.v111 R.v112 N.v112 R.v113 N.v113 R.v114 N.v114 R.v115 N.v115 R.v116 N.v116 R.v117 N.v117 R.v118 N.v118 R.v119 N.v119 R.v120 N.v120 R.v121 N.v121 R.v122 N.v122 R.v123 N.v123 R.v124 N.v124 R.v125 N.v125 R.v126 N.v126 R.v127 N.v127 R.v128 N.v128 R.v129 N.v129 R.v130 N.v130 R.v131 N.v131 R.v132 N.v132 R.v133 N.v133 R.v134 N.v134 R.v135 N.v135 R.v136 N.v136 R.v137 N.v137 R.v138 N.v138 R.v139 N.v139 R.v140 N.v140 R.v141 N.v141 R.v142 N.v142 R.v143 N.v143 R.v144 N.v144 R.v145 N.v145 R.v146 N.v146 R.v147 N.v147 R.v148 N.v148 R.v149 N.v149 R.v150 N.v150 R.v151 N.v151 R.v152 N.v152 R.v153 N.v153 R.v154 N.v154 R.v155 N.v155 R.v156 N.v156 R.v157 N.v157 R.v158 N.v158 R.v159 N.v159 R.v160 N.v160 R.v161 N.v161 R.v162 N.v162 R.v163 N.v163 R.v164 N.v164 R.v165 N.v165 R.v166 N.v166 R.v167 N.v167 R.v168 N.v168 R.v169 N.v169 R.v170 N.v170 R.v171 N.v171 R.v172 N.v172 R.v173 N.v173 R.v174 N.v174 R.v175 N.v175 R.v176 N.v176 R.v177 N.v177 R.v178 N.v178 R.v179 N.v179 R.v180 N.v180 R.v181 N.v181 R.v182 N.v182 R.v183 N.v183 R.v184 N.v184 R.v185 N.v185 R.v186 N.v186 R.v187 N.v187 R.v188 N.v188 R.v189 N.v189 R.v190 N.v190 R.v191 N.v191 R.v192 N.v192 R.v193 N.v193 R.v194 N.v194 R.v195 N.v195 R.v196 N.v196 R.v197 N.v197 R.v198 N.v198 R.v199 N.v199 R.v200 N.v200 R.v201 N.v201 R.v202 N.v202 R.v203 N.v203 R.v204 N.v204 R.v205 N.v205 R.v206 N.v206 R.v207 N.v207 R.v208 N.v208 R.v209 N.v209 R.v210 N.v210 R.v211 N.v211 R.v212 N.v212 R.v213 N.v213 R.v214 N.v214 R.v215 N.v215 R.v216 N.v216 R.v217 N.v217 R.v218 N.v218 R.v219 N.v219 R.v220 N.v220 R.v221 N.v221 R.v222 N.v222 R.v223 N.v223 R.v224 N.v224 R.v225 N.v225 R.v226 N.v226 R.v227 N.v227 R.v228 N.v228 R.v229 N.v229 R.v230 N.v230 R.v231 N.v231 R.v232 N.v232 R.v233 N.v233 R.v234 N.v234 R.v235 N.v235 R.v236 N.v236 R.v237 N.v237 R.v238 N.v238 R.v239 N.v239 R.v240 N.v240 R.v241 N.v241 R.v242 N.v242 R.v243 N.v243 R.v244 N.v244 R.v245 N.v245 R.v246 N.v246 R.v247 N.v247 R.v248 N.v248 R.v249 N.v249 R.v250 N.v250 R.v251 N.v251 R.v252 N.v252 R.v253 N.v253 R.v254 N.v254 R.v255 N.v255 R.v256 N.v256 R.v257 N.v257 R.v258 N.v258 R.v259 N.v259 R.v260 N.v260 R.v261 N.v261 R.v262 N.v262 R.v263 N.v263 R.v264 N.v264 R.v265 N.v265 R.v266 N.v266 R.v267 N.v267 R.v268 N.v268 R.v269 N.v269 R.v270 N.v270 R.v271 N.v271 R.v272 N.v272 R.v273 N.v273 R.v274 N.v274 R.v275 N.v275 R.v276 N.v276 R.v277 N.v277 R.v278 N.v278 R.v279 N.v279 R.v280 N.v280 R.v281 N.v281 R.v282 N.v282 R.v283 N.v283 R.v284 N.v284 R.v285 N.v285 R.v286 N.v286 R.v287 N.v287.
Theorem checks_refine s i : R.assertionChecks (state s) (inputs i) = N.assertionChecks s i.
Proof. unfold R.assertionChecks, N.assertionChecks.
  rewrite ?node_38.
  rewrite ?node_226.
  rewrite ?node_229.
  rewrite ?node_231.
  rewrite ?node_232.
  rewrite ?node_234.
  rewrite ?node_264.
  rewrite ?node_266.
  rewrite ?node_270.
  rewrite ?node_273.
  rewrite ?node_282.
  rewrite ?node_283.
  rewrite ?node_284.
  rewrite ?node_285.
  rewrite ?node_286.
  rewrite ?node_287.
  reflexivity.
Qed.
Theorem asserts_refine s i : N.asserts s i <-> R.asserts (state s) (inputs i).
Proof. unfold N.asserts, R.asserts; rewrite checks_refine; reflexivity. Qed.
Print Assumptions step_refines.
Print Assumptions observe_refines.
Print Assumptions run_refines.
Print Assumptions asserts_refine.
End MulDivCheckedRefinement.
