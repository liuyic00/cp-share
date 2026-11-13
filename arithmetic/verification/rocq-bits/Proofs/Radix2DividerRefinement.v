(* Generated proof certificates, checked by Rocq. *)
From Stdlib Require Import ZArith Lia List Bool Zmod.Bits.
From BitsGenerated Require Import Radix2Divider.
From ReferenceGenerated Require Import Radix2Divider.
From BitsProofs Require Import Unsigned BitFacts RefinementTactics.
Module Radix2DividerRefinement.
Module N := BitsGenerated.Radix2Divider.nRadix2Divider.
Module R := ReferenceGenerated.Radix2Divider.nRadix2Divider.
Module NB := BitsGenerated.Radix2Divider.CIRCTBits.
Module RB := ReferenceGenerated.Radix2Divider.CIRCTBits.
Open Scope Z_scope.
Definition inputs (x : N.Inputs) : R.Inputs := R.mkInputs
  (Zmod.unsigned (N.nreset x))
  (Zmod.unsigned (N.nio_5Fin_5Fvalid x))
  (Zmod.unsigned (N.nio_5Fin_5Fbits_5Fsrc_5F0 x))
  (Zmod.unsigned (N.nio_5Fin_5Fbits_5Fsrc_5F1 x))
  (Zmod.unsigned (N.nio_5Fin_5Fbits_5Fsrc_5F2 x))
  (Zmod.unsigned (N.nio_5Fout_5Fready x))
  (Zmod.unsigned (N.nctrl_5Fsign x))
  (Zmod.unsigned (N.nctrl_5FisW x))
  (Zmod.unsigned (N.nctrl_5FisHi x)).
Lemma inputs_nreset x : R.nreset (inputs x) = Zmod.unsigned (N.nreset x). Proof. reflexivity. Qed.
Lemma inputs_nio_5Fin_5Fvalid x : R.nio_5Fin_5Fvalid (inputs x) = Zmod.unsigned (N.nio_5Fin_5Fvalid x). Proof. reflexivity. Qed.
Lemma inputs_nio_5Fin_5Fbits_5Fsrc_5F0 x : R.nio_5Fin_5Fbits_5Fsrc_5F0 (inputs x) = Zmod.unsigned (N.nio_5Fin_5Fbits_5Fsrc_5F0 x). Proof. reflexivity. Qed.
Lemma inputs_nio_5Fin_5Fbits_5Fsrc_5F1 x : R.nio_5Fin_5Fbits_5Fsrc_5F1 (inputs x) = Zmod.unsigned (N.nio_5Fin_5Fbits_5Fsrc_5F1 x). Proof. reflexivity. Qed.
Lemma inputs_nio_5Fin_5Fbits_5Fsrc_5F2 x : R.nio_5Fin_5Fbits_5Fsrc_5F2 (inputs x) = Zmod.unsigned (N.nio_5Fin_5Fbits_5Fsrc_5F2 x). Proof. reflexivity. Qed.
Lemma inputs_nio_5Fout_5Fready x : R.nio_5Fout_5Fready (inputs x) = Zmod.unsigned (N.nio_5Fout_5Fready x). Proof. reflexivity. Qed.
Lemma inputs_nctrl_5Fsign x : R.nctrl_5Fsign (inputs x) = Zmod.unsigned (N.nctrl_5Fsign x). Proof. reflexivity. Qed.
Lemma inputs_nctrl_5FisW x : R.nctrl_5FisW (inputs x) = Zmod.unsigned (N.nctrl_5FisW x). Proof. reflexivity. Qed.
Lemma inputs_nctrl_5FisHi x : R.nctrl_5FisHi (inputs x) = Zmod.unsigned (N.nctrl_5FisHi x). Proof. reflexivity. Qed.
Definition state (x : N.State) : R.State := R.mkState
  (Zmod.unsigned (N.r0_nstate x))
  (Zmod.unsigned (N.r1_ndivBy0Reg x))
  (Zmod.unsigned (N.r2_nshiftReg x))
  (Zmod.unsigned (N.r3_naSignReg x))
  (Zmod.unsigned (N.r4_nqSignReg x))
  (Zmod.unsigned (N.r5_nbReg x))
  (Zmod.unsigned (N.r6_naValx2Reg x))
  (Zmod.unsigned (N.r7_nctrlReg_5FisW x))
  (Zmod.unsigned (N.r8_nctrlReg_5FisHi x))
  (Zmod.unsigned (N.r9_ncnt_5Fvalue x))
  (Zmod.unsigned (N.r10_nhistoryValid x))
  (Zmod.unsigned (N.r11_npreviousState x))
  (Zmod.unsigned (N.r12_npreviousCount x))
  (Zmod.unsigned (N.r13_nwasStalled x))
  (Zmod.unsigned (N.r14_npreviousOutput x)).
Lemma state_r0_nstate x : R.r0_nstate (state x) = Zmod.unsigned (N.r0_nstate x). Proof. reflexivity. Qed.
Lemma state_r1_ndivBy0Reg x : R.r1_ndivBy0Reg (state x) = Zmod.unsigned (N.r1_ndivBy0Reg x). Proof. reflexivity. Qed.
Lemma state_r2_nshiftReg x : R.r2_nshiftReg (state x) = Zmod.unsigned (N.r2_nshiftReg x). Proof. reflexivity. Qed.
Lemma state_r3_naSignReg x : R.r3_naSignReg (state x) = Zmod.unsigned (N.r3_naSignReg x). Proof. reflexivity. Qed.
Lemma state_r4_nqSignReg x : R.r4_nqSignReg (state x) = Zmod.unsigned (N.r4_nqSignReg x). Proof. reflexivity. Qed.
Lemma state_r5_nbReg x : R.r5_nbReg (state x) = Zmod.unsigned (N.r5_nbReg x). Proof. reflexivity. Qed.
Lemma state_r6_naValx2Reg x : R.r6_naValx2Reg (state x) = Zmod.unsigned (N.r6_naValx2Reg x). Proof. reflexivity. Qed.
Lemma state_r7_nctrlReg_5FisW x : R.r7_nctrlReg_5FisW (state x) = Zmod.unsigned (N.r7_nctrlReg_5FisW x). Proof. reflexivity. Qed.
Lemma state_r8_nctrlReg_5FisHi x : R.r8_nctrlReg_5FisHi (state x) = Zmod.unsigned (N.r8_nctrlReg_5FisHi x). Proof. reflexivity. Qed.
Lemma state_r9_ncnt_5Fvalue x : R.r9_ncnt_5Fvalue (state x) = Zmod.unsigned (N.r9_ncnt_5Fvalue x). Proof. reflexivity. Qed.
Lemma state_r10_nhistoryValid x : R.r10_nhistoryValid (state x) = Zmod.unsigned (N.r10_nhistoryValid x). Proof. reflexivity. Qed.
Lemma state_r11_npreviousState x : R.r11_npreviousState (state x) = Zmod.unsigned (N.r11_npreviousState x). Proof. reflexivity. Qed.
Lemma state_r12_npreviousCount x : R.r12_npreviousCount (state x) = Zmod.unsigned (N.r12_npreviousCount x). Proof. reflexivity. Qed.
Lemma state_r13_nwasStalled x : R.r13_nwasStalled (state x) = Zmod.unsigned (N.r13_nwasStalled x). Proof. reflexivity. Qed.
Lemma state_r14_npreviousOutput x : R.r14_npreviousOutput (state x) = Zmod.unsigned (N.r14_npreviousOutput x). Proof. reflexivity. Qed.
Definition outputs (x : N.Outputs) : R.Outputs := R.mkOutputs
  (Zmod.unsigned (N.nio_5Fin_5Fready x))
  (Zmod.unsigned (N.nio_5Fout_5Fvalid x))
  (Zmod.unsigned (N.nio_5Fout_5Fbits_5Fdata x)).
Lemma outputs_nio_5Fin_5Fready x : R.nio_5Fin_5Fready (outputs x) = Zmod.unsigned (N.nio_5Fin_5Fready x). Proof. reflexivity. Qed.
Lemma outputs_nio_5Fout_5Fvalid x : R.nio_5Fout_5Fvalid (outputs x) = Zmod.unsigned (N.nio_5Fout_5Fvalid x). Proof. reflexivity. Qed.
Lemma outputs_nio_5Fout_5Fbits_5Fdata x : R.nio_5Fout_5Fbits_5Fdata (outputs x) = Zmod.unsigned (N.nio_5Fout_5Fbits_5Fdata x). Proof. reflexivity. Qed.
Lemma repeat_32 (x : bits 1) : RB.repeatWord 32 1 (Zmod.unsigned x) mod 2^32 = Zmod.unsigned (NB.repeatBits 32 32 x).
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
  rewrite !inputs_nio_5Fin_5Fvalid.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fin_5Fvalid i)).
  finish_numeric.
Qed.
Lemma node_3 (s : N.State) (i : N.Inputs) : R.v3 (state s) (inputs i) = Zmod.unsigned (N.v3 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v3 s i)) at 1; unfold R.v3, N.v3.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_4 (s : N.State) (i : N.Inputs) : R.v4 (state s) (inputs i) = Zmod.unsigned (N.v4 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v4 s i)) at 1; unfold R.v4, N.v4.
  unfold R.v3, N.v3.
  rewrite !state_r0_nstate.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r0_nstate s)).
  finish_numeric.
Qed.
Lemma node_5 (s : N.State) (i : N.Inputs) : R.v5 (state s) (inputs i) = Zmod.unsigned (N.v5 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v5 s i)) at 1; unfold R.v5, N.v5.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_6 (s : N.State) (i : N.Inputs) : R.v6 (state s) (inputs i) = Zmod.unsigned (N.v6 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v6 s i)) at 1; unfold R.v6, N.v6.
  unfold R.v5, N.v5.
  rewrite !state_r0_nstate.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r0_nstate s)).
  finish_numeric.
Qed.
Lemma node_7 (s : N.State) (i : N.Inputs) : R.v7 (state s) (inputs i) = Zmod.unsigned (N.v7 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v7 s i)) at 1; unfold R.v7, N.v7.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_8 (s : N.State) (i : N.Inputs) : R.v8 (state s) (inputs i) = Zmod.unsigned (N.v8 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v8 s i)) at 1; unfold R.v8, N.v8.
  unfold R.v7, N.v7.
  rewrite !state_r0_nstate.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r0_nstate s)).
  finish_numeric.
Qed.
Lemma node_9 (s : N.State) (i : N.Inputs) : R.v9 (state s) (inputs i) = Zmod.unsigned (N.v9 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v9 s i)) at 1; unfold R.v9, N.v9.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_10 (s : N.State) (i : N.Inputs) : R.v10 (state s) (inputs i) = Zmod.unsigned (N.v10 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v10 s i)) at 1; unfold R.v10, N.v10.
  unfold R.v9, N.v9.
  rewrite !state_r9_ncnt_5Fvalue.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r9_ncnt_5Fvalue s)).
  finish_numeric.
Qed.
Lemma node_11 (s : N.State) (i : N.Inputs) : R.v11 (state s) (inputs i) = Zmod.unsigned (N.v11 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v11 s i)) at 1; unfold R.v11, N.v11.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_12 (s : N.State) (i : N.Inputs) : R.v12 (state s) (inputs i) = Zmod.unsigned (N.v12 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v12 s i)) at 1; unfold R.v12, N.v12.
  rewrite ?node_10.
  unfold R.v11, N.v11.
  rewrite !state_r0_nstate.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r0_nstate s)).
  finish_numeric.
Qed.
Lemma node_13 (s : N.State) (i : N.Inputs) : R.v13 (state s) (inputs i) = Zmod.unsigned (N.v13 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v13 s i)) at 1; unfold R.v13, N.v13.
  unfold R.v11, N.v11.
  rewrite !state_r0_nstate.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r0_nstate s)).
  finish_numeric.
Qed.
Lemma node_14 (s : N.State) (i : N.Inputs) : R.v14 (state s) (inputs i) = Zmod.unsigned (N.v14 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v14 s i)) at 1; unfold R.v14, N.v14.
  rewrite ?node_13.
  rewrite !inputs_nio_5Fout_5Fready.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fout_5Fready i)).
  finish_numeric.
Qed.
Lemma node_15 (s : N.State) (i : N.Inputs) : R.v15 (state s) (inputs i) = Zmod.unsigned (N.v15 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v15 s i)) at 1; unfold R.v15, N.v15.
  unfold R.v0, N.v0.
  rewrite ?node_14.
  rewrite !state_r0_nstate.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r0_nstate s)).
  finish_numeric.
Qed.
Lemma node_16 (s : N.State) (i : N.Inputs) : R.v16 (state s) (inputs i) = Zmod.unsigned (N.v16 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v16 s i)) at 1; unfold R.v16, N.v16.
  rewrite ?node_8.
  rewrite ?node_12.
  rewrite ?node_15.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_17 (s : N.State) (i : N.Inputs) : R.v17 (state s) (inputs i) = Zmod.unsigned (N.v17 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v17 s i)) at 1; unfold R.v17, N.v17.
  rewrite ?node_6.
  unfold R.v7, N.v7.
  rewrite ?node_16.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_18 (s : N.State) (i : N.Inputs) : R.v18 (state s) (inputs i) = Zmod.unsigned (N.v18 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v18 s i)) at 1; unfold R.v18, N.v18.
  rewrite ?node_4.
  unfold R.v5, N.v5.
  rewrite ?node_17.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_19 (s : N.State) (i : N.Inputs) : R.v19 (state s) (inputs i) = Zmod.unsigned (N.v19 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v19 s i)) at 1; unfold R.v19, N.v19.
  rewrite ?node_2.
  unfold R.v3, N.v3.
  rewrite ?node_18.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_20 (s : N.State) (i : N.Inputs) : R.v20 (state s) (inputs i) = Zmod.unsigned (N.v20 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v20 s i)) at 1; unfold R.v20, N.v20.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_21 (s : N.State) (i : N.Inputs) : R.v21 (state s) (inputs i) = Zmod.unsigned (N.v21 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v21 s i)) at 1; unfold R.v21, N.v21.
  unfold R.v20, N.v20.
  rewrite !inputs_nio_5Fin_5Fbits_5Fsrc_5F1.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fin_5Fbits_5Fsrc_5F1 i)).
  finish_numeric.
Qed.
Lemma node_22 (s : N.State) (i : N.Inputs) : R.v22 (state s) (inputs i) = Zmod.unsigned (N.v22 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v22 s i)) at 1; unfold R.v22, N.v22.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_23 (s : N.State) (i : N.Inputs) : R.v23 (state s) (inputs i) = Zmod.unsigned (N.v23 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v23 s i)) at 1; unfold R.v23, N.v23.
  rewrite ?node_21.
  unfold R.v22, N.v22.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_24 (s : N.State) (i : N.Inputs) : R.v24 (state s) (inputs i) = Zmod.unsigned (N.v24 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v24 s i)) at 1; unfold R.v24, N.v24.
  rewrite ?node_2.
  rewrite ?node_23.
  rewrite !state_r1_ndivBy0Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r1_ndivBy0Reg s)).
  finish_numeric.
Qed.
Lemma node_25 (s : N.State) (i : N.Inputs) : R.v25 (state s) (inputs i) = Zmod.unsigned (N.v25 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v25 s i)) at 1; unfold R.v25, N.v25.
  rewrite ?node_2.
  rewrite ?node_4.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_26 (s : N.State) (i : N.Inputs) : R.v26 (state s) (inputs i) = Zmod.unsigned (N.v26 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v26 s i)) at 1; unfold R.v26, N.v26.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_27 (s : N.State) (i : N.Inputs) : R.v27 (state s) (inputs i) = Zmod.unsigned (N.v27 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v27 s i)) at 1; unfold R.v27, N.v27.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_28 (s : N.State) (i : N.Inputs) : R.v28 (state s) (inputs i) = Zmod.unsigned (N.v28 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v28 s i)) at 1; unfold R.v28, N.v28.
  unfold R.v27, N.v27.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_29 (s : N.State) (i : N.Inputs) : R.v29 (state s) (inputs i) = Zmod.unsigned (N.v29 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v29 s i)) at 1; unfold R.v29, N.v29.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_30 (s : N.State) (i : N.Inputs) : R.v30 (state s) (inputs i) = Zmod.unsigned (N.v30 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v30 s i)) at 1; unfold R.v30, N.v30.
  unfold R.v29, N.v29.
  rewrite !state_r9_ncnt_5Fvalue.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r9_ncnt_5Fvalue s)).
  finish_numeric.
Qed.
Lemma node_31 (s : N.State) (i : N.Inputs) : R.v31 (state s) (inputs i) = Zmod.unsigned (N.v31 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v31 s i)) at 1; unfold R.v31, N.v31.
  rewrite ?node_28.
  rewrite ?node_30.
  unfold RB.word.
  pose proof (bits.unsigned_range (N.v28 s i) ltac:(lia)).
  pose proof (bits.unsigned_range (N.v30 s i) ltac:(lia)).
  finish_numeric.
Qed.
Lemma node_32 (s : N.State) (i : N.Inputs) : R.v32 (state s) (inputs i) = Zmod.unsigned (N.v32 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v32 s i)) at 1; unfold R.v32, N.v32.
  unfold R.v26, N.v26.
  rewrite ?node_31.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_33 (s : N.State) (i : N.Inputs) : R.v33 (state s) (inputs i) = Zmod.unsigned (N.v33 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v33 s i)) at 1; unfold R.v33, N.v33.
  rewrite !state_r2_nshiftReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r2_nshiftReg s)).
  finish_numeric.
Qed.
Lemma node_34 (s : N.State) (i : N.Inputs) : R.v34 (state s) (inputs i) = Zmod.unsigned (N.v34 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v34 s i)) at 1; unfold R.v34, N.v34.
  unfold R.v26, N.v26.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_35 (s : N.State) (i : N.Inputs) : R.v35 (state s) (inputs i) = Zmod.unsigned (N.v35 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v35 s i)) at 1; unfold R.v35, N.v35.
  rewrite ?node_33.
  rewrite ?node_34.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_36 (s : N.State) (i : N.Inputs) : R.v36 (state s) (inputs i) = Zmod.unsigned (N.v36 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v36 s i)) at 1; unfold R.v36, N.v36.
  rewrite !state_r2_nshiftReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r2_nshiftReg s)).
  finish_numeric.
Qed.
Lemma node_37 (s : N.State) (i : N.Inputs) : R.v37 (state s) (inputs i) = Zmod.unsigned (N.v37 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v37 s i)) at 1; unfold R.v37, N.v37.
  rewrite ?node_36.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_38 (s : N.State) (i : N.Inputs) : R.v38 (state s) (inputs i) = Zmod.unsigned (N.v38 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v38 s i)) at 1; unfold R.v38, N.v38.
  rewrite !state_r2_nshiftReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r2_nshiftReg s)).
  finish_numeric.
Qed.
Lemma node_39 (s : N.State) (i : N.Inputs) : R.v39 (state s) (inputs i) = Zmod.unsigned (N.v39 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v39 s i)) at 1; unfold R.v39, N.v39.
  rewrite ?node_35.
  rewrite ?node_37.
  rewrite ?node_38.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_40 (s : N.State) (i : N.Inputs) : R.v40 (state s) (inputs i) = Zmod.unsigned (N.v40 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v40 s i)) at 1; unfold R.v40, N.v40.
  rewrite !state_r2_nshiftReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r2_nshiftReg s)).
  finish_numeric.
Qed.
Lemma node_41 (s : N.State) (i : N.Inputs) : R.v41 (state s) (inputs i) = Zmod.unsigned (N.v41 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v41 s i)) at 1; unfold R.v41, N.v41.
  rewrite ?node_35.
  rewrite ?node_39.
  rewrite ?node_40.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_42 (s : N.State) (i : N.Inputs) : R.v42 (state s) (inputs i) = Zmod.unsigned (N.v42 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v42 s i)) at 1; unfold R.v42, N.v42.
  rewrite ?node_8.
  rewrite ?node_41.
  rewrite !state_r2_nshiftReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r2_nshiftReg s)).
  finish_numeric.
Qed.
Lemma node_43 (s : N.State) (i : N.Inputs) : R.v43 (state s) (inputs i) = Zmod.unsigned (N.v43 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v43 s i)) at 1; unfold R.v43, N.v43.
  rewrite ?node_6.
  rewrite ?node_32.
  rewrite ?node_42.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_44 (s : N.State) (i : N.Inputs) : R.v44 (state s) (inputs i) = Zmod.unsigned (N.v44 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v44 s i)) at 1; unfold R.v44, N.v44.
  rewrite ?node_25.
  rewrite ?node_43.
  rewrite !state_r2_nshiftReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r2_nshiftReg s)).
  finish_numeric.
Qed.
Lemma node_45 (s : N.State) (i : N.Inputs) : R.v45 (state s) (inputs i) = Zmod.unsigned (N.v45 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v45 s i)) at 1; unfold R.v45, N.v45.
  rewrite !inputs_nio_5Fin_5Fbits_5Fsrc_5F0.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fin_5Fbits_5Fsrc_5F0 i)).
  finish_numeric.
Qed.
Lemma node_46 (s : N.State) (i : N.Inputs) : R.v46 (state s) (inputs i) = Zmod.unsigned (N.v46 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v46 s i)) at 1; unfold R.v46, N.v46.
  rewrite ?node_45.
  rewrite !inputs_nctrl_5Fsign.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nctrl_5Fsign i)).
  finish_numeric.
Qed.
Lemma node_47 (s : N.State) (i : N.Inputs) : R.v47 (state s) (inputs i) = Zmod.unsigned (N.v47 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v47 s i)) at 1; unfold R.v47, N.v47.
  rewrite ?node_2.
  rewrite ?node_46.
  rewrite !state_r3_naSignReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r3_naSignReg s)).
  finish_numeric.
Qed.
Lemma node_48 (s : N.State) (i : N.Inputs) : R.v48 (state s) (inputs i) = Zmod.unsigned (N.v48 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v48 s i)) at 1; unfold R.v48, N.v48.
  rewrite !inputs_nio_5Fin_5Fbits_5Fsrc_5F1.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fin_5Fbits_5Fsrc_5F1 i)).
  finish_numeric.
Qed.
Lemma node_49 (s : N.State) (i : N.Inputs) : R.v49 (state s) (inputs i) = Zmod.unsigned (N.v49 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v49 s i)) at 1; unfold R.v49, N.v49.
  rewrite ?node_48.
  rewrite !inputs_nctrl_5Fsign.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nctrl_5Fsign i)).
  finish_numeric.
Qed.
Lemma node_50 (s : N.State) (i : N.Inputs) : R.v50 (state s) (inputs i) = Zmod.unsigned (N.v50 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v50 s i)) at 1; unfold R.v50, N.v50.
  rewrite ?node_46.
  rewrite ?node_49.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_51 (s : N.State) (i : N.Inputs) : R.v51 (state s) (inputs i) = Zmod.unsigned (N.v51 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v51 s i)) at 1; unfold R.v51, N.v51.
  rewrite ?node_21.
  rewrite ?node_50.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_52 (s : N.State) (i : N.Inputs) : R.v52 (state s) (inputs i) = Zmod.unsigned (N.v52 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v52 s i)) at 1; unfold R.v52, N.v52.
  rewrite ?node_2.
  rewrite ?node_51.
  rewrite !state_r4_nqSignReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r4_nqSignReg s)).
  finish_numeric.
Qed.
Lemma node_53 (s : N.State) (i : N.Inputs) : R.v53 (state s) (inputs i) = Zmod.unsigned (N.v53 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v53 s i)) at 1; unfold R.v53, N.v53.
  unfold R.v20, N.v20.
  rewrite !inputs_nio_5Fin_5Fbits_5Fsrc_5F1.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fin_5Fbits_5Fsrc_5F1 i)).
  finish_numeric.
Qed.
Lemma node_54 (s : N.State) (i : N.Inputs) : R.v54 (state s) (inputs i) = Zmod.unsigned (N.v54 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v54 s i)) at 1; unfold R.v54, N.v54.
  rewrite ?node_49.
  rewrite ?node_53.
  rewrite !inputs_nio_5Fin_5Fbits_5Fsrc_5F1.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fin_5Fbits_5Fsrc_5F1 i)).
  finish_numeric.
Qed.
Lemma node_55 (s : N.State) (i : N.Inputs) : R.v55 (state s) (inputs i) = Zmod.unsigned (N.v55 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v55 s i)) at 1; unfold R.v55, N.v55.
  rewrite ?node_2.
  rewrite ?node_54.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_56 (s : N.State) (i : N.Inputs) : R.v56 (state s) (inputs i) = Zmod.unsigned (N.v56 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v56 s i)) at 1; unfold R.v56, N.v56.
  unfold R.v20, N.v20.
  rewrite !inputs_nio_5Fin_5Fbits_5Fsrc_5F0.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fin_5Fbits_5Fsrc_5F0 i)).
  finish_numeric.
Qed.
Lemma node_57 (s : N.State) (i : N.Inputs) : R.v57 (state s) (inputs i) = Zmod.unsigned (N.v57 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v57 s i)) at 1; unfold R.v57, N.v57.
  rewrite ?node_46.
  rewrite ?node_56.
  rewrite !inputs_nio_5Fin_5Fbits_5Fsrc_5F0.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fin_5Fbits_5Fsrc_5F0 i)).
  finish_numeric.
Qed.
Lemma node_58 (s : N.State) (i : N.Inputs) : R.v58 (state s) (inputs i) = Zmod.unsigned (N.v58 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v58 s i)) at 1; unfold R.v58, N.v58.
  unfold R.v26, N.v26.
  rewrite ?node_57.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_59 (s : N.State) (i : N.Inputs) : R.v59 (state s) (inputs i) = Zmod.unsigned (N.v59 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v59 s i)) at 1; unfold R.v59, N.v59.
  rewrite ?node_2.
  rewrite ?node_58.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_60 (s : N.State) (i : N.Inputs) : R.v60 (state s) (inputs i) = Zmod.unsigned (N.v60 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v60 s i)) at 1; unfold R.v60, N.v60.
  rewrite ?node_2.
  rewrite !inputs_nctrl_5FisW.
  rewrite !state_r7_nctrlReg_5FisW.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nctrl_5FisW i)).
  rewrite ?(bits.mod_to_Z (N.r7_nctrlReg_5FisW s)).
  finish_numeric.
Qed.
Lemma node_61 (s : N.State) (i : N.Inputs) : R.v61 (state s) (inputs i) = Zmod.unsigned (N.v61 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v61 s i)) at 1; unfold R.v61, N.v61.
  rewrite ?node_2.
  rewrite !inputs_nctrl_5FisHi.
  rewrite !state_r8_nctrlReg_5FisHi.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nctrl_5FisHi i)).
  rewrite ?(bits.mod_to_Z (N.r8_nctrlReg_5FisHi s)).
  finish_numeric.
Qed.
Lemma node_62 (s : N.State) (i : N.Inputs) : R.v62 (state s) (inputs i) = Zmod.unsigned (N.v62 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v62 s i)) at 1; unfold R.v62, N.v62.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_63 (s : N.State) (i : N.Inputs) : R.v63 (state s) (inputs i) = Zmod.unsigned (N.v63 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v63 s i)) at 1; unfold R.v63, N.v63.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_64 (s : N.State) (i : N.Inputs) : R.v64 (state s) (inputs i) = Zmod.unsigned (N.v64 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v64 s i)) at 1; unfold R.v64, N.v64.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_65 (s : N.State) (i : N.Inputs) : R.v65 (state s) (inputs i) = Zmod.unsigned (N.v65 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v65 s i)) at 1; unfold R.v65, N.v65.
  rewrite ?node_63.
  unfold R.v64, N.v64.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_66 (s : N.State) (i : N.Inputs) : R.v66 (state s) (inputs i) = Zmod.unsigned (N.v66 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v66 s i)) at 1; unfold R.v66, N.v66.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_67 (s : N.State) (i : N.Inputs) : R.v67 (state s) (inputs i) = Zmod.unsigned (N.v67 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v67 s i)) at 1; unfold R.v67, N.v67.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_68 (s : N.State) (i : N.Inputs) : R.v68 (state s) (inputs i) = Zmod.unsigned (N.v68 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v68 s i)) at 1; unfold R.v68, N.v68.
  rewrite ?node_66.
  unfold R.v67, N.v67.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_69 (s : N.State) (i : N.Inputs) : R.v69 (state s) (inputs i) = Zmod.unsigned (N.v69 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v69 s i)) at 1; unfold R.v69, N.v69.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_70 (s : N.State) (i : N.Inputs) : R.v70 (state s) (inputs i) = Zmod.unsigned (N.v70 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v70 s i)) at 1; unfold R.v70, N.v70.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_71 (s : N.State) (i : N.Inputs) : R.v71 (state s) (inputs i) = Zmod.unsigned (N.v71 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v71 s i)) at 1; unfold R.v71, N.v71.
  rewrite ?node_69.
  unfold R.v70, N.v70.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_72 (s : N.State) (i : N.Inputs) : R.v72 (state s) (inputs i) = Zmod.unsigned (N.v72 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v72 s i)) at 1; unfold R.v72, N.v72.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_73 (s : N.State) (i : N.Inputs) : R.v73 (state s) (inputs i) = Zmod.unsigned (N.v73 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v73 s i)) at 1; unfold R.v73, N.v73.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_74 (s : N.State) (i : N.Inputs) : R.v74 (state s) (inputs i) = Zmod.unsigned (N.v74 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v74 s i)) at 1; unfold R.v74, N.v74.
  rewrite ?node_72.
  unfold R.v73, N.v73.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_75 (s : N.State) (i : N.Inputs) : R.v75 (state s) (inputs i) = Zmod.unsigned (N.v75 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v75 s i)) at 1; unfold R.v75, N.v75.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_76 (s : N.State) (i : N.Inputs) : R.v76 (state s) (inputs i) = Zmod.unsigned (N.v76 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v76 s i)) at 1; unfold R.v76, N.v76.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_77 (s : N.State) (i : N.Inputs) : R.v77 (state s) (inputs i) = Zmod.unsigned (N.v77 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v77 s i)) at 1; unfold R.v77, N.v77.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_78 (s : N.State) (i : N.Inputs) : R.v78 (state s) (inputs i) = Zmod.unsigned (N.v78 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v78 s i)) at 1; unfold R.v78, N.v78.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_79 (s : N.State) (i : N.Inputs) : R.v79 (state s) (inputs i) = Zmod.unsigned (N.v79 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v79 s i)) at 1; unfold R.v79, N.v79.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_80 (s : N.State) (i : N.Inputs) : R.v80 (state s) (inputs i) = Zmod.unsigned (N.v80 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v80 s i)) at 1; unfold R.v80, N.v80.
  unfold R.v26, N.v26.
  rewrite ?node_79.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_81 (s : N.State) (i : N.Inputs) : R.v81 (state s) (inputs i) = Zmod.unsigned (N.v81 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v81 s i)) at 1; unfold R.v81, N.v81.
  rewrite ?node_77.
  unfold R.v78, N.v78.
  rewrite ?node_80.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_82 (s : N.State) (i : N.Inputs) : R.v82 (state s) (inputs i) = Zmod.unsigned (N.v82 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v82 s i)) at 1; unfold R.v82, N.v82.
  rewrite ?node_75.
  unfold R.v76, N.v76.
  rewrite ?node_81.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_83 (s : N.State) (i : N.Inputs) : R.v83 (state s) (inputs i) = Zmod.unsigned (N.v83 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v83 s i)) at 1; unfold R.v83, N.v83.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_84 (s : N.State) (i : N.Inputs) : R.v84 (state s) (inputs i) = Zmod.unsigned (N.v84 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v84 s i)) at 1; unfold R.v84, N.v84.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_85 (s : N.State) (i : N.Inputs) : R.v85 (state s) (inputs i) = Zmod.unsigned (N.v85 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v85 s i)) at 1; unfold R.v85, N.v85.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_86 (s : N.State) (i : N.Inputs) : R.v86 (state s) (inputs i) = Zmod.unsigned (N.v86 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v86 s i)) at 1; unfold R.v86, N.v86.
  unfold R.v26, N.v26.
  rewrite ?node_85.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_87 (s : N.State) (i : N.Inputs) : R.v87 (state s) (inputs i) = Zmod.unsigned (N.v87 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v87 s i)) at 1; unfold R.v87, N.v87.
  unfold R.v78, N.v78.
  rewrite ?node_84.
  rewrite ?node_86.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_88 (s : N.State) (i : N.Inputs) : R.v88 (state s) (inputs i) = Zmod.unsigned (N.v88 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v88 s i)) at 1; unfold R.v88, N.v88.
  unfold R.v76, N.v76.
  rewrite ?node_83.
  rewrite ?node_87.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_89 (s : N.State) (i : N.Inputs) : R.v89 (state s) (inputs i) = Zmod.unsigned (N.v89 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v89 s i)) at 1; unfold R.v89, N.v89.
  rewrite ?node_74.
  rewrite ?node_82.
  rewrite ?node_88.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_90 (s : N.State) (i : N.Inputs) : R.v90 (state s) (inputs i) = Zmod.unsigned (N.v90 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v90 s i)) at 1; unfold R.v90, N.v90.
  rewrite ?node_74.
  rewrite ?node_89.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_91 (s : N.State) (i : N.Inputs) : R.v91 (state s) (inputs i) = Zmod.unsigned (N.v91 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v91 s i)) at 1; unfold R.v91, N.v91.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_92 (s : N.State) (i : N.Inputs) : R.v92 (state s) (inputs i) = Zmod.unsigned (N.v92 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v92 s i)) at 1; unfold R.v92, N.v92.
  unfold R.v73, N.v73.
  rewrite ?node_91.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_93 (s : N.State) (i : N.Inputs) : R.v93 (state s) (inputs i) = Zmod.unsigned (N.v93 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v93 s i)) at 1; unfold R.v93, N.v93.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_94 (s : N.State) (i : N.Inputs) : R.v94 (state s) (inputs i) = Zmod.unsigned (N.v94 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v94 s i)) at 1; unfold R.v94, N.v94.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_95 (s : N.State) (i : N.Inputs) : R.v95 (state s) (inputs i) = Zmod.unsigned (N.v95 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v95 s i)) at 1; unfold R.v95, N.v95.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_96 (s : N.State) (i : N.Inputs) : R.v96 (state s) (inputs i) = Zmod.unsigned (N.v96 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v96 s i)) at 1; unfold R.v96, N.v96.
  unfold R.v26, N.v26.
  rewrite ?node_95.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_97 (s : N.State) (i : N.Inputs) : R.v97 (state s) (inputs i) = Zmod.unsigned (N.v97 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v97 s i)) at 1; unfold R.v97, N.v97.
  unfold R.v78, N.v78.
  rewrite ?node_94.
  rewrite ?node_96.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_98 (s : N.State) (i : N.Inputs) : R.v98 (state s) (inputs i) = Zmod.unsigned (N.v98 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v98 s i)) at 1; unfold R.v98, N.v98.
  unfold R.v76, N.v76.
  rewrite ?node_93.
  rewrite ?node_97.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_99 (s : N.State) (i : N.Inputs) : R.v99 (state s) (inputs i) = Zmod.unsigned (N.v99 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v99 s i)) at 1; unfold R.v99, N.v99.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_100 (s : N.State) (i : N.Inputs) : R.v100 (state s) (inputs i) = Zmod.unsigned (N.v100 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v100 s i)) at 1; unfold R.v100, N.v100.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_101 (s : N.State) (i : N.Inputs) : R.v101 (state s) (inputs i) = Zmod.unsigned (N.v101 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v101 s i)) at 1; unfold R.v101, N.v101.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_102 (s : N.State) (i : N.Inputs) : R.v102 (state s) (inputs i) = Zmod.unsigned (N.v102 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v102 s i)) at 1; unfold R.v102, N.v102.
  unfold R.v26, N.v26.
  rewrite ?node_101.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_103 (s : N.State) (i : N.Inputs) : R.v103 (state s) (inputs i) = Zmod.unsigned (N.v103 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v103 s i)) at 1; unfold R.v103, N.v103.
  unfold R.v78, N.v78.
  rewrite ?node_100.
  rewrite ?node_102.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_104 (s : N.State) (i : N.Inputs) : R.v104 (state s) (inputs i) = Zmod.unsigned (N.v104 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v104 s i)) at 1; unfold R.v104, N.v104.
  unfold R.v76, N.v76.
  rewrite ?node_99.
  rewrite ?node_103.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_105 (s : N.State) (i : N.Inputs) : R.v105 (state s) (inputs i) = Zmod.unsigned (N.v105 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v105 s i)) at 1; unfold R.v105, N.v105.
  rewrite ?node_92.
  rewrite ?node_98.
  rewrite ?node_104.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_106 (s : N.State) (i : N.Inputs) : R.v106 (state s) (inputs i) = Zmod.unsigned (N.v106 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v106 s i)) at 1; unfold R.v106, N.v106.
  rewrite ?node_92.
  rewrite ?node_105.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_107 (s : N.State) (i : N.Inputs) : R.v107 (state s) (inputs i) = Zmod.unsigned (N.v107 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v107 s i)) at 1; unfold R.v107, N.v107.
  rewrite ?node_71.
  rewrite ?node_90.
  rewrite ?node_106.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_108 (s : N.State) (i : N.Inputs) : R.v108 (state s) (inputs i) = Zmod.unsigned (N.v108 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v108 s i)) at 1; unfold R.v108, N.v108.
  rewrite ?node_71.
  rewrite ?node_107.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_109 (s : N.State) (i : N.Inputs) : R.v109 (state s) (inputs i) = Zmod.unsigned (N.v109 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v109 s i)) at 1; unfold R.v109, N.v109.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_110 (s : N.State) (i : N.Inputs) : R.v110 (state s) (inputs i) = Zmod.unsigned (N.v110 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v110 s i)) at 1; unfold R.v110, N.v110.
  unfold R.v70, N.v70.
  rewrite ?node_109.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_111 (s : N.State) (i : N.Inputs) : R.v111 (state s) (inputs i) = Zmod.unsigned (N.v111 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v111 s i)) at 1; unfold R.v111, N.v111.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_112 (s : N.State) (i : N.Inputs) : R.v112 (state s) (inputs i) = Zmod.unsigned (N.v112 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v112 s i)) at 1; unfold R.v112, N.v112.
  unfold R.v73, N.v73.
  rewrite ?node_111.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_113 (s : N.State) (i : N.Inputs) : R.v113 (state s) (inputs i) = Zmod.unsigned (N.v113 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v113 s i)) at 1; unfold R.v113, N.v113.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_114 (s : N.State) (i : N.Inputs) : R.v114 (state s) (inputs i) = Zmod.unsigned (N.v114 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v114 s i)) at 1; unfold R.v114, N.v114.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_115 (s : N.State) (i : N.Inputs) : R.v115 (state s) (inputs i) = Zmod.unsigned (N.v115 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v115 s i)) at 1; unfold R.v115, N.v115.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_116 (s : N.State) (i : N.Inputs) : R.v116 (state s) (inputs i) = Zmod.unsigned (N.v116 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v116 s i)) at 1; unfold R.v116, N.v116.
  unfold R.v26, N.v26.
  rewrite ?node_115.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_117 (s : N.State) (i : N.Inputs) : R.v117 (state s) (inputs i) = Zmod.unsigned (N.v117 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v117 s i)) at 1; unfold R.v117, N.v117.
  unfold R.v78, N.v78.
  rewrite ?node_114.
  rewrite ?node_116.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_118 (s : N.State) (i : N.Inputs) : R.v118 (state s) (inputs i) = Zmod.unsigned (N.v118 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v118 s i)) at 1; unfold R.v118, N.v118.
  unfold R.v76, N.v76.
  rewrite ?node_113.
  rewrite ?node_117.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_119 (s : N.State) (i : N.Inputs) : R.v119 (state s) (inputs i) = Zmod.unsigned (N.v119 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v119 s i)) at 1; unfold R.v119, N.v119.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_120 (s : N.State) (i : N.Inputs) : R.v120 (state s) (inputs i) = Zmod.unsigned (N.v120 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v120 s i)) at 1; unfold R.v120, N.v120.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_121 (s : N.State) (i : N.Inputs) : R.v121 (state s) (inputs i) = Zmod.unsigned (N.v121 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v121 s i)) at 1; unfold R.v121, N.v121.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_122 (s : N.State) (i : N.Inputs) : R.v122 (state s) (inputs i) = Zmod.unsigned (N.v122 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v122 s i)) at 1; unfold R.v122, N.v122.
  unfold R.v26, N.v26.
  rewrite ?node_121.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_123 (s : N.State) (i : N.Inputs) : R.v123 (state s) (inputs i) = Zmod.unsigned (N.v123 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v123 s i)) at 1; unfold R.v123, N.v123.
  unfold R.v78, N.v78.
  rewrite ?node_120.
  rewrite ?node_122.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_124 (s : N.State) (i : N.Inputs) : R.v124 (state s) (inputs i) = Zmod.unsigned (N.v124 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v124 s i)) at 1; unfold R.v124, N.v124.
  unfold R.v76, N.v76.
  rewrite ?node_119.
  rewrite ?node_123.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_125 (s : N.State) (i : N.Inputs) : R.v125 (state s) (inputs i) = Zmod.unsigned (N.v125 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v125 s i)) at 1; unfold R.v125, N.v125.
  rewrite ?node_112.
  rewrite ?node_118.
  rewrite ?node_124.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_126 (s : N.State) (i : N.Inputs) : R.v126 (state s) (inputs i) = Zmod.unsigned (N.v126 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v126 s i)) at 1; unfold R.v126, N.v126.
  rewrite ?node_112.
  rewrite ?node_125.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_127 (s : N.State) (i : N.Inputs) : R.v127 (state s) (inputs i) = Zmod.unsigned (N.v127 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v127 s i)) at 1; unfold R.v127, N.v127.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_128 (s : N.State) (i : N.Inputs) : R.v128 (state s) (inputs i) = Zmod.unsigned (N.v128 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v128 s i)) at 1; unfold R.v128, N.v128.
  unfold R.v73, N.v73.
  rewrite ?node_127.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_129 (s : N.State) (i : N.Inputs) : R.v129 (state s) (inputs i) = Zmod.unsigned (N.v129 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v129 s i)) at 1; unfold R.v129, N.v129.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_130 (s : N.State) (i : N.Inputs) : R.v130 (state s) (inputs i) = Zmod.unsigned (N.v130 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v130 s i)) at 1; unfold R.v130, N.v130.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_131 (s : N.State) (i : N.Inputs) : R.v131 (state s) (inputs i) = Zmod.unsigned (N.v131 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v131 s i)) at 1; unfold R.v131, N.v131.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_132 (s : N.State) (i : N.Inputs) : R.v132 (state s) (inputs i) = Zmod.unsigned (N.v132 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v132 s i)) at 1; unfold R.v132, N.v132.
  unfold R.v26, N.v26.
  rewrite ?node_131.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_133 (s : N.State) (i : N.Inputs) : R.v133 (state s) (inputs i) = Zmod.unsigned (N.v133 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v133 s i)) at 1; unfold R.v133, N.v133.
  unfold R.v78, N.v78.
  rewrite ?node_130.
  rewrite ?node_132.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_134 (s : N.State) (i : N.Inputs) : R.v134 (state s) (inputs i) = Zmod.unsigned (N.v134 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v134 s i)) at 1; unfold R.v134, N.v134.
  unfold R.v76, N.v76.
  rewrite ?node_129.
  rewrite ?node_133.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_135 (s : N.State) (i : N.Inputs) : R.v135 (state s) (inputs i) = Zmod.unsigned (N.v135 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v135 s i)) at 1; unfold R.v135, N.v135.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_136 (s : N.State) (i : N.Inputs) : R.v136 (state s) (inputs i) = Zmod.unsigned (N.v136 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v136 s i)) at 1; unfold R.v136, N.v136.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_137 (s : N.State) (i : N.Inputs) : R.v137 (state s) (inputs i) = Zmod.unsigned (N.v137 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v137 s i)) at 1; unfold R.v137, N.v137.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_138 (s : N.State) (i : N.Inputs) : R.v138 (state s) (inputs i) = Zmod.unsigned (N.v138 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v138 s i)) at 1; unfold R.v138, N.v138.
  unfold R.v26, N.v26.
  rewrite ?node_137.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_139 (s : N.State) (i : N.Inputs) : R.v139 (state s) (inputs i) = Zmod.unsigned (N.v139 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v139 s i)) at 1; unfold R.v139, N.v139.
  unfold R.v78, N.v78.
  rewrite ?node_136.
  rewrite ?node_138.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_140 (s : N.State) (i : N.Inputs) : R.v140 (state s) (inputs i) = Zmod.unsigned (N.v140 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v140 s i)) at 1; unfold R.v140, N.v140.
  unfold R.v76, N.v76.
  rewrite ?node_135.
  rewrite ?node_139.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_141 (s : N.State) (i : N.Inputs) : R.v141 (state s) (inputs i) = Zmod.unsigned (N.v141 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v141 s i)) at 1; unfold R.v141, N.v141.
  rewrite ?node_128.
  rewrite ?node_134.
  rewrite ?node_140.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_142 (s : N.State) (i : N.Inputs) : R.v142 (state s) (inputs i) = Zmod.unsigned (N.v142 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v142 s i)) at 1; unfold R.v142, N.v142.
  rewrite ?node_128.
  rewrite ?node_141.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_143 (s : N.State) (i : N.Inputs) : R.v143 (state s) (inputs i) = Zmod.unsigned (N.v143 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v143 s i)) at 1; unfold R.v143, N.v143.
  rewrite ?node_110.
  rewrite ?node_126.
  rewrite ?node_142.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_144 (s : N.State) (i : N.Inputs) : R.v144 (state s) (inputs i) = Zmod.unsigned (N.v144 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v144 s i)) at 1; unfold R.v144, N.v144.
  rewrite ?node_110.
  rewrite ?node_143.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_145 (s : N.State) (i : N.Inputs) : R.v145 (state s) (inputs i) = Zmod.unsigned (N.v145 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v145 s i)) at 1; unfold R.v145, N.v145.
  rewrite ?node_68.
  rewrite ?node_108.
  rewrite ?node_144.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_146 (s : N.State) (i : N.Inputs) : R.v146 (state s) (inputs i) = Zmod.unsigned (N.v146 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v146 s i)) at 1; unfold R.v146, N.v146.
  rewrite ?node_68.
  rewrite ?node_145.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_147 (s : N.State) (i : N.Inputs) : R.v147 (state s) (inputs i) = Zmod.unsigned (N.v147 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v147 s i)) at 1; unfold R.v147, N.v147.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_148 (s : N.State) (i : N.Inputs) : R.v148 (state s) (inputs i) = Zmod.unsigned (N.v148 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v148 s i)) at 1; unfold R.v148, N.v148.
  unfold R.v67, N.v67.
  rewrite ?node_147.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_149 (s : N.State) (i : N.Inputs) : R.v149 (state s) (inputs i) = Zmod.unsigned (N.v149 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v149 s i)) at 1; unfold R.v149, N.v149.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_150 (s : N.State) (i : N.Inputs) : R.v150 (state s) (inputs i) = Zmod.unsigned (N.v150 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v150 s i)) at 1; unfold R.v150, N.v150.
  unfold R.v70, N.v70.
  rewrite ?node_149.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_151 (s : N.State) (i : N.Inputs) : R.v151 (state s) (inputs i) = Zmod.unsigned (N.v151 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v151 s i)) at 1; unfold R.v151, N.v151.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_152 (s : N.State) (i : N.Inputs) : R.v152 (state s) (inputs i) = Zmod.unsigned (N.v152 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v152 s i)) at 1; unfold R.v152, N.v152.
  unfold R.v73, N.v73.
  rewrite ?node_151.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_153 (s : N.State) (i : N.Inputs) : R.v153 (state s) (inputs i) = Zmod.unsigned (N.v153 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v153 s i)) at 1; unfold R.v153, N.v153.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_154 (s : N.State) (i : N.Inputs) : R.v154 (state s) (inputs i) = Zmod.unsigned (N.v154 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v154 s i)) at 1; unfold R.v154, N.v154.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_155 (s : N.State) (i : N.Inputs) : R.v155 (state s) (inputs i) = Zmod.unsigned (N.v155 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v155 s i)) at 1; unfold R.v155, N.v155.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_156 (s : N.State) (i : N.Inputs) : R.v156 (state s) (inputs i) = Zmod.unsigned (N.v156 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v156 s i)) at 1; unfold R.v156, N.v156.
  unfold R.v26, N.v26.
  rewrite ?node_155.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_157 (s : N.State) (i : N.Inputs) : R.v157 (state s) (inputs i) = Zmod.unsigned (N.v157 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v157 s i)) at 1; unfold R.v157, N.v157.
  unfold R.v78, N.v78.
  rewrite ?node_154.
  rewrite ?node_156.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_158 (s : N.State) (i : N.Inputs) : R.v158 (state s) (inputs i) = Zmod.unsigned (N.v158 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v158 s i)) at 1; unfold R.v158, N.v158.
  unfold R.v76, N.v76.
  rewrite ?node_153.
  rewrite ?node_157.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_159 (s : N.State) (i : N.Inputs) : R.v159 (state s) (inputs i) = Zmod.unsigned (N.v159 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v159 s i)) at 1; unfold R.v159, N.v159.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_160 (s : N.State) (i : N.Inputs) : R.v160 (state s) (inputs i) = Zmod.unsigned (N.v160 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v160 s i)) at 1; unfold R.v160, N.v160.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_161 (s : N.State) (i : N.Inputs) : R.v161 (state s) (inputs i) = Zmod.unsigned (N.v161 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v161 s i)) at 1; unfold R.v161, N.v161.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_162 (s : N.State) (i : N.Inputs) : R.v162 (state s) (inputs i) = Zmod.unsigned (N.v162 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v162 s i)) at 1; unfold R.v162, N.v162.
  unfold R.v26, N.v26.
  rewrite ?node_161.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_163 (s : N.State) (i : N.Inputs) : R.v163 (state s) (inputs i) = Zmod.unsigned (N.v163 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v163 s i)) at 1; unfold R.v163, N.v163.
  unfold R.v78, N.v78.
  rewrite ?node_160.
  rewrite ?node_162.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_164 (s : N.State) (i : N.Inputs) : R.v164 (state s) (inputs i) = Zmod.unsigned (N.v164 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v164 s i)) at 1; unfold R.v164, N.v164.
  unfold R.v76, N.v76.
  rewrite ?node_159.
  rewrite ?node_163.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_165 (s : N.State) (i : N.Inputs) : R.v165 (state s) (inputs i) = Zmod.unsigned (N.v165 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v165 s i)) at 1; unfold R.v165, N.v165.
  rewrite ?node_152.
  rewrite ?node_158.
  rewrite ?node_164.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_166 (s : N.State) (i : N.Inputs) : R.v166 (state s) (inputs i) = Zmod.unsigned (N.v166 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v166 s i)) at 1; unfold R.v166, N.v166.
  rewrite ?node_152.
  rewrite ?node_165.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_167 (s : N.State) (i : N.Inputs) : R.v167 (state s) (inputs i) = Zmod.unsigned (N.v167 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v167 s i)) at 1; unfold R.v167, N.v167.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_168 (s : N.State) (i : N.Inputs) : R.v168 (state s) (inputs i) = Zmod.unsigned (N.v168 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v168 s i)) at 1; unfold R.v168, N.v168.
  unfold R.v73, N.v73.
  rewrite ?node_167.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_169 (s : N.State) (i : N.Inputs) : R.v169 (state s) (inputs i) = Zmod.unsigned (N.v169 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v169 s i)) at 1; unfold R.v169, N.v169.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_170 (s : N.State) (i : N.Inputs) : R.v170 (state s) (inputs i) = Zmod.unsigned (N.v170 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v170 s i)) at 1; unfold R.v170, N.v170.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_171 (s : N.State) (i : N.Inputs) : R.v171 (state s) (inputs i) = Zmod.unsigned (N.v171 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v171 s i)) at 1; unfold R.v171, N.v171.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_172 (s : N.State) (i : N.Inputs) : R.v172 (state s) (inputs i) = Zmod.unsigned (N.v172 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v172 s i)) at 1; unfold R.v172, N.v172.
  unfold R.v26, N.v26.
  rewrite ?node_171.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_173 (s : N.State) (i : N.Inputs) : R.v173 (state s) (inputs i) = Zmod.unsigned (N.v173 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v173 s i)) at 1; unfold R.v173, N.v173.
  unfold R.v78, N.v78.
  rewrite ?node_170.
  rewrite ?node_172.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_174 (s : N.State) (i : N.Inputs) : R.v174 (state s) (inputs i) = Zmod.unsigned (N.v174 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v174 s i)) at 1; unfold R.v174, N.v174.
  unfold R.v76, N.v76.
  rewrite ?node_169.
  rewrite ?node_173.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_175 (s : N.State) (i : N.Inputs) : R.v175 (state s) (inputs i) = Zmod.unsigned (N.v175 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v175 s i)) at 1; unfold R.v175, N.v175.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_176 (s : N.State) (i : N.Inputs) : R.v176 (state s) (inputs i) = Zmod.unsigned (N.v176 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v176 s i)) at 1; unfold R.v176, N.v176.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_177 (s : N.State) (i : N.Inputs) : R.v177 (state s) (inputs i) = Zmod.unsigned (N.v177 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v177 s i)) at 1; unfold R.v177, N.v177.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_178 (s : N.State) (i : N.Inputs) : R.v178 (state s) (inputs i) = Zmod.unsigned (N.v178 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v178 s i)) at 1; unfold R.v178, N.v178.
  unfold R.v26, N.v26.
  rewrite ?node_177.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_179 (s : N.State) (i : N.Inputs) : R.v179 (state s) (inputs i) = Zmod.unsigned (N.v179 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v179 s i)) at 1; unfold R.v179, N.v179.
  unfold R.v78, N.v78.
  rewrite ?node_176.
  rewrite ?node_178.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_180 (s : N.State) (i : N.Inputs) : R.v180 (state s) (inputs i) = Zmod.unsigned (N.v180 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v180 s i)) at 1; unfold R.v180, N.v180.
  unfold R.v76, N.v76.
  rewrite ?node_175.
  rewrite ?node_179.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_181 (s : N.State) (i : N.Inputs) : R.v181 (state s) (inputs i) = Zmod.unsigned (N.v181 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v181 s i)) at 1; unfold R.v181, N.v181.
  rewrite ?node_168.
  rewrite ?node_174.
  rewrite ?node_180.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_182 (s : N.State) (i : N.Inputs) : R.v182 (state s) (inputs i) = Zmod.unsigned (N.v182 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v182 s i)) at 1; unfold R.v182, N.v182.
  rewrite ?node_168.
  rewrite ?node_181.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_183 (s : N.State) (i : N.Inputs) : R.v183 (state s) (inputs i) = Zmod.unsigned (N.v183 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v183 s i)) at 1; unfold R.v183, N.v183.
  rewrite ?node_150.
  rewrite ?node_166.
  rewrite ?node_182.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_184 (s : N.State) (i : N.Inputs) : R.v184 (state s) (inputs i) = Zmod.unsigned (N.v184 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v184 s i)) at 1; unfold R.v184, N.v184.
  rewrite ?node_150.
  rewrite ?node_183.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_185 (s : N.State) (i : N.Inputs) : R.v185 (state s) (inputs i) = Zmod.unsigned (N.v185 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v185 s i)) at 1; unfold R.v185, N.v185.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_186 (s : N.State) (i : N.Inputs) : R.v186 (state s) (inputs i) = Zmod.unsigned (N.v186 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v186 s i)) at 1; unfold R.v186, N.v186.
  unfold R.v70, N.v70.
  rewrite ?node_185.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_187 (s : N.State) (i : N.Inputs) : R.v187 (state s) (inputs i) = Zmod.unsigned (N.v187 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v187 s i)) at 1; unfold R.v187, N.v187.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_188 (s : N.State) (i : N.Inputs) : R.v188 (state s) (inputs i) = Zmod.unsigned (N.v188 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v188 s i)) at 1; unfold R.v188, N.v188.
  unfold R.v73, N.v73.
  rewrite ?node_187.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_189 (s : N.State) (i : N.Inputs) : R.v189 (state s) (inputs i) = Zmod.unsigned (N.v189 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v189 s i)) at 1; unfold R.v189, N.v189.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_190 (s : N.State) (i : N.Inputs) : R.v190 (state s) (inputs i) = Zmod.unsigned (N.v190 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v190 s i)) at 1; unfold R.v190, N.v190.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_191 (s : N.State) (i : N.Inputs) : R.v191 (state s) (inputs i) = Zmod.unsigned (N.v191 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v191 s i)) at 1; unfold R.v191, N.v191.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_192 (s : N.State) (i : N.Inputs) : R.v192 (state s) (inputs i) = Zmod.unsigned (N.v192 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v192 s i)) at 1; unfold R.v192, N.v192.
  unfold R.v26, N.v26.
  rewrite ?node_191.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_193 (s : N.State) (i : N.Inputs) : R.v193 (state s) (inputs i) = Zmod.unsigned (N.v193 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v193 s i)) at 1; unfold R.v193, N.v193.
  unfold R.v78, N.v78.
  rewrite ?node_190.
  rewrite ?node_192.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_194 (s : N.State) (i : N.Inputs) : R.v194 (state s) (inputs i) = Zmod.unsigned (N.v194 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v194 s i)) at 1; unfold R.v194, N.v194.
  unfold R.v76, N.v76.
  rewrite ?node_189.
  rewrite ?node_193.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_195 (s : N.State) (i : N.Inputs) : R.v195 (state s) (inputs i) = Zmod.unsigned (N.v195 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v195 s i)) at 1; unfold R.v195, N.v195.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_196 (s : N.State) (i : N.Inputs) : R.v196 (state s) (inputs i) = Zmod.unsigned (N.v196 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v196 s i)) at 1; unfold R.v196, N.v196.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_197 (s : N.State) (i : N.Inputs) : R.v197 (state s) (inputs i) = Zmod.unsigned (N.v197 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v197 s i)) at 1; unfold R.v197, N.v197.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_198 (s : N.State) (i : N.Inputs) : R.v198 (state s) (inputs i) = Zmod.unsigned (N.v198 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v198 s i)) at 1; unfold R.v198, N.v198.
  unfold R.v26, N.v26.
  rewrite ?node_197.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_199 (s : N.State) (i : N.Inputs) : R.v199 (state s) (inputs i) = Zmod.unsigned (N.v199 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v199 s i)) at 1; unfold R.v199, N.v199.
  unfold R.v78, N.v78.
  rewrite ?node_196.
  rewrite ?node_198.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_200 (s : N.State) (i : N.Inputs) : R.v200 (state s) (inputs i) = Zmod.unsigned (N.v200 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v200 s i)) at 1; unfold R.v200, N.v200.
  unfold R.v76, N.v76.
  rewrite ?node_195.
  rewrite ?node_199.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_201 (s : N.State) (i : N.Inputs) : R.v201 (state s) (inputs i) = Zmod.unsigned (N.v201 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v201 s i)) at 1; unfold R.v201, N.v201.
  rewrite ?node_188.
  rewrite ?node_194.
  rewrite ?node_200.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_202 (s : N.State) (i : N.Inputs) : R.v202 (state s) (inputs i) = Zmod.unsigned (N.v202 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v202 s i)) at 1; unfold R.v202, N.v202.
  rewrite ?node_188.
  rewrite ?node_201.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_203 (s : N.State) (i : N.Inputs) : R.v203 (state s) (inputs i) = Zmod.unsigned (N.v203 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v203 s i)) at 1; unfold R.v203, N.v203.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_204 (s : N.State) (i : N.Inputs) : R.v204 (state s) (inputs i) = Zmod.unsigned (N.v204 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v204 s i)) at 1; unfold R.v204, N.v204.
  unfold R.v73, N.v73.
  rewrite ?node_203.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_205 (s : N.State) (i : N.Inputs) : R.v205 (state s) (inputs i) = Zmod.unsigned (N.v205 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v205 s i)) at 1; unfold R.v205, N.v205.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_206 (s : N.State) (i : N.Inputs) : R.v206 (state s) (inputs i) = Zmod.unsigned (N.v206 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v206 s i)) at 1; unfold R.v206, N.v206.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_207 (s : N.State) (i : N.Inputs) : R.v207 (state s) (inputs i) = Zmod.unsigned (N.v207 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v207 s i)) at 1; unfold R.v207, N.v207.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_208 (s : N.State) (i : N.Inputs) : R.v208 (state s) (inputs i) = Zmod.unsigned (N.v208 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v208 s i)) at 1; unfold R.v208, N.v208.
  unfold R.v26, N.v26.
  rewrite ?node_207.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_209 (s : N.State) (i : N.Inputs) : R.v209 (state s) (inputs i) = Zmod.unsigned (N.v209 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v209 s i)) at 1; unfold R.v209, N.v209.
  unfold R.v78, N.v78.
  rewrite ?node_206.
  rewrite ?node_208.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_210 (s : N.State) (i : N.Inputs) : R.v210 (state s) (inputs i) = Zmod.unsigned (N.v210 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v210 s i)) at 1; unfold R.v210, N.v210.
  unfold R.v76, N.v76.
  rewrite ?node_205.
  rewrite ?node_209.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_211 (s : N.State) (i : N.Inputs) : R.v211 (state s) (inputs i) = Zmod.unsigned (N.v211 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v211 s i)) at 1; unfold R.v211, N.v211.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_212 (s : N.State) (i : N.Inputs) : R.v212 (state s) (inputs i) = Zmod.unsigned (N.v212 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v212 s i)) at 1; unfold R.v212, N.v212.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_213 (s : N.State) (i : N.Inputs) : R.v213 (state s) (inputs i) = Zmod.unsigned (N.v213 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v213 s i)) at 1; unfold R.v213, N.v213.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_214 (s : N.State) (i : N.Inputs) : R.v214 (state s) (inputs i) = Zmod.unsigned (N.v214 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v214 s i)) at 1; unfold R.v214, N.v214.
  unfold R.v26, N.v26.
  rewrite ?node_213.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_215 (s : N.State) (i : N.Inputs) : R.v215 (state s) (inputs i) = Zmod.unsigned (N.v215 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v215 s i)) at 1; unfold R.v215, N.v215.
  unfold R.v78, N.v78.
  rewrite ?node_212.
  rewrite ?node_214.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_216 (s : N.State) (i : N.Inputs) : R.v216 (state s) (inputs i) = Zmod.unsigned (N.v216 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v216 s i)) at 1; unfold R.v216, N.v216.
  unfold R.v76, N.v76.
  rewrite ?node_211.
  rewrite ?node_215.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_217 (s : N.State) (i : N.Inputs) : R.v217 (state s) (inputs i) = Zmod.unsigned (N.v217 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v217 s i)) at 1; unfold R.v217, N.v217.
  rewrite ?node_204.
  rewrite ?node_210.
  rewrite ?node_216.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_218 (s : N.State) (i : N.Inputs) : R.v218 (state s) (inputs i) = Zmod.unsigned (N.v218 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v218 s i)) at 1; unfold R.v218, N.v218.
  rewrite ?node_204.
  rewrite ?node_217.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_219 (s : N.State) (i : N.Inputs) : R.v219 (state s) (inputs i) = Zmod.unsigned (N.v219 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v219 s i)) at 1; unfold R.v219, N.v219.
  rewrite ?node_186.
  rewrite ?node_202.
  rewrite ?node_218.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_220 (s : N.State) (i : N.Inputs) : R.v220 (state s) (inputs i) = Zmod.unsigned (N.v220 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v220 s i)) at 1; unfold R.v220, N.v220.
  rewrite ?node_186.
  rewrite ?node_219.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_221 (s : N.State) (i : N.Inputs) : R.v221 (state s) (inputs i) = Zmod.unsigned (N.v221 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v221 s i)) at 1; unfold R.v221, N.v221.
  rewrite ?node_148.
  rewrite ?node_184.
  rewrite ?node_220.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_222 (s : N.State) (i : N.Inputs) : R.v222 (state s) (inputs i) = Zmod.unsigned (N.v222 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v222 s i)) at 1; unfold R.v222, N.v222.
  rewrite ?node_148.
  rewrite ?node_221.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_223 (s : N.State) (i : N.Inputs) : R.v223 (state s) (inputs i) = Zmod.unsigned (N.v223 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v223 s i)) at 1; unfold R.v223, N.v223.
  rewrite ?node_65.
  rewrite ?node_146.
  rewrite ?node_222.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_224 (s : N.State) (i : N.Inputs) : R.v224 (state s) (inputs i) = Zmod.unsigned (N.v224 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v224 s i)) at 1; unfold R.v224, N.v224.
  unfold R.v26, N.v26.
  rewrite ?node_65.
  rewrite ?node_223.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_225 (s : N.State) (i : N.Inputs) : R.v225 (state s) (inputs i) = Zmod.unsigned (N.v225 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v225 s i)) at 1; unfold R.v225, N.v225.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_226 (s : N.State) (i : N.Inputs) : R.v226 (state s) (inputs i) = Zmod.unsigned (N.v226 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v226 s i)) at 1; unfold R.v226, N.v226.
  rewrite ?node_224.
  unfold R.v225, N.v225.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_227 (s : N.State) (i : N.Inputs) : R.v227 (state s) (inputs i) = Zmod.unsigned (N.v227 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v227 s i)) at 1; unfold R.v227, N.v227.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_228 (s : N.State) (i : N.Inputs) : R.v228 (state s) (inputs i) = Zmod.unsigned (N.v228 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v228 s i)) at 1; unfold R.v228, N.v228.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_229 (s : N.State) (i : N.Inputs) : R.v229 (state s) (inputs i) = Zmod.unsigned (N.v229 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v229 s i)) at 1; unfold R.v229, N.v229.
  unfold R.v64, N.v64.
  rewrite ?node_228.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_230 (s : N.State) (i : N.Inputs) : R.v230 (state s) (inputs i) = Zmod.unsigned (N.v230 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v230 s i)) at 1; unfold R.v230, N.v230.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_231 (s : N.State) (i : N.Inputs) : R.v231 (state s) (inputs i) = Zmod.unsigned (N.v231 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v231 s i)) at 1; unfold R.v231, N.v231.
  unfold R.v67, N.v67.
  rewrite ?node_230.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_232 (s : N.State) (i : N.Inputs) : R.v232 (state s) (inputs i) = Zmod.unsigned (N.v232 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v232 s i)) at 1; unfold R.v232, N.v232.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_233 (s : N.State) (i : N.Inputs) : R.v233 (state s) (inputs i) = Zmod.unsigned (N.v233 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v233 s i)) at 1; unfold R.v233, N.v233.
  unfold R.v70, N.v70.
  rewrite ?node_232.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_234 (s : N.State) (i : N.Inputs) : R.v234 (state s) (inputs i) = Zmod.unsigned (N.v234 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v234 s i)) at 1; unfold R.v234, N.v234.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_235 (s : N.State) (i : N.Inputs) : R.v235 (state s) (inputs i) = Zmod.unsigned (N.v235 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v235 s i)) at 1; unfold R.v235, N.v235.
  unfold R.v73, N.v73.
  rewrite ?node_234.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_236 (s : N.State) (i : N.Inputs) : R.v236 (state s) (inputs i) = Zmod.unsigned (N.v236 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v236 s i)) at 1; unfold R.v236, N.v236.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_237 (s : N.State) (i : N.Inputs) : R.v237 (state s) (inputs i) = Zmod.unsigned (N.v237 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v237 s i)) at 1; unfold R.v237, N.v237.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_238 (s : N.State) (i : N.Inputs) : R.v238 (state s) (inputs i) = Zmod.unsigned (N.v238 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v238 s i)) at 1; unfold R.v238, N.v238.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_239 (s : N.State) (i : N.Inputs) : R.v239 (state s) (inputs i) = Zmod.unsigned (N.v239 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v239 s i)) at 1; unfold R.v239, N.v239.
  unfold R.v26, N.v26.
  rewrite ?node_238.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_240 (s : N.State) (i : N.Inputs) : R.v240 (state s) (inputs i) = Zmod.unsigned (N.v240 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v240 s i)) at 1; unfold R.v240, N.v240.
  unfold R.v78, N.v78.
  rewrite ?node_237.
  rewrite ?node_239.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_241 (s : N.State) (i : N.Inputs) : R.v241 (state s) (inputs i) = Zmod.unsigned (N.v241 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v241 s i)) at 1; unfold R.v241, N.v241.
  unfold R.v76, N.v76.
  rewrite ?node_236.
  rewrite ?node_240.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_242 (s : N.State) (i : N.Inputs) : R.v242 (state s) (inputs i) = Zmod.unsigned (N.v242 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v242 s i)) at 1; unfold R.v242, N.v242.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_243 (s : N.State) (i : N.Inputs) : R.v243 (state s) (inputs i) = Zmod.unsigned (N.v243 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v243 s i)) at 1; unfold R.v243, N.v243.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_244 (s : N.State) (i : N.Inputs) : R.v244 (state s) (inputs i) = Zmod.unsigned (N.v244 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v244 s i)) at 1; unfold R.v244, N.v244.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_245 (s : N.State) (i : N.Inputs) : R.v245 (state s) (inputs i) = Zmod.unsigned (N.v245 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v245 s i)) at 1; unfold R.v245, N.v245.
  unfold R.v26, N.v26.
  rewrite ?node_244.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_246 (s : N.State) (i : N.Inputs) : R.v246 (state s) (inputs i) = Zmod.unsigned (N.v246 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v246 s i)) at 1; unfold R.v246, N.v246.
  unfold R.v78, N.v78.
  rewrite ?node_243.
  rewrite ?node_245.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_247 (s : N.State) (i : N.Inputs) : R.v247 (state s) (inputs i) = Zmod.unsigned (N.v247 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v247 s i)) at 1; unfold R.v247, N.v247.
  unfold R.v76, N.v76.
  rewrite ?node_242.
  rewrite ?node_246.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_248 (s : N.State) (i : N.Inputs) : R.v248 (state s) (inputs i) = Zmod.unsigned (N.v248 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v248 s i)) at 1; unfold R.v248, N.v248.
  rewrite ?node_235.
  rewrite ?node_241.
  rewrite ?node_247.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_249 (s : N.State) (i : N.Inputs) : R.v249 (state s) (inputs i) = Zmod.unsigned (N.v249 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v249 s i)) at 1; unfold R.v249, N.v249.
  rewrite ?node_235.
  rewrite ?node_248.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_250 (s : N.State) (i : N.Inputs) : R.v250 (state s) (inputs i) = Zmod.unsigned (N.v250 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v250 s i)) at 1; unfold R.v250, N.v250.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_251 (s : N.State) (i : N.Inputs) : R.v251 (state s) (inputs i) = Zmod.unsigned (N.v251 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v251 s i)) at 1; unfold R.v251, N.v251.
  unfold R.v73, N.v73.
  rewrite ?node_250.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_252 (s : N.State) (i : N.Inputs) : R.v252 (state s) (inputs i) = Zmod.unsigned (N.v252 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v252 s i)) at 1; unfold R.v252, N.v252.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_253 (s : N.State) (i : N.Inputs) : R.v253 (state s) (inputs i) = Zmod.unsigned (N.v253 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v253 s i)) at 1; unfold R.v253, N.v253.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_254 (s : N.State) (i : N.Inputs) : R.v254 (state s) (inputs i) = Zmod.unsigned (N.v254 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v254 s i)) at 1; unfold R.v254, N.v254.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_255 (s : N.State) (i : N.Inputs) : R.v255 (state s) (inputs i) = Zmod.unsigned (N.v255 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v255 s i)) at 1; unfold R.v255, N.v255.
  unfold R.v26, N.v26.
  rewrite ?node_254.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_256 (s : N.State) (i : N.Inputs) : R.v256 (state s) (inputs i) = Zmod.unsigned (N.v256 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v256 s i)) at 1; unfold R.v256, N.v256.
  unfold R.v78, N.v78.
  rewrite ?node_253.
  rewrite ?node_255.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_257 (s : N.State) (i : N.Inputs) : R.v257 (state s) (inputs i) = Zmod.unsigned (N.v257 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v257 s i)) at 1; unfold R.v257, N.v257.
  unfold R.v76, N.v76.
  rewrite ?node_252.
  rewrite ?node_256.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_258 (s : N.State) (i : N.Inputs) : R.v258 (state s) (inputs i) = Zmod.unsigned (N.v258 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v258 s i)) at 1; unfold R.v258, N.v258.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_259 (s : N.State) (i : N.Inputs) : R.v259 (state s) (inputs i) = Zmod.unsigned (N.v259 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v259 s i)) at 1; unfold R.v259, N.v259.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_260 (s : N.State) (i : N.Inputs) : R.v260 (state s) (inputs i) = Zmod.unsigned (N.v260 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v260 s i)) at 1; unfold R.v260, N.v260.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_261 (s : N.State) (i : N.Inputs) : R.v261 (state s) (inputs i) = Zmod.unsigned (N.v261 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v261 s i)) at 1; unfold R.v261, N.v261.
  unfold R.v26, N.v26.
  rewrite ?node_260.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_262 (s : N.State) (i : N.Inputs) : R.v262 (state s) (inputs i) = Zmod.unsigned (N.v262 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v262 s i)) at 1; unfold R.v262, N.v262.
  unfold R.v78, N.v78.
  rewrite ?node_259.
  rewrite ?node_261.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_263 (s : N.State) (i : N.Inputs) : R.v263 (state s) (inputs i) = Zmod.unsigned (N.v263 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v263 s i)) at 1; unfold R.v263, N.v263.
  unfold R.v76, N.v76.
  rewrite ?node_258.
  rewrite ?node_262.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_264 (s : N.State) (i : N.Inputs) : R.v264 (state s) (inputs i) = Zmod.unsigned (N.v264 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v264 s i)) at 1; unfold R.v264, N.v264.
  rewrite ?node_251.
  rewrite ?node_257.
  rewrite ?node_263.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_265 (s : N.State) (i : N.Inputs) : R.v265 (state s) (inputs i) = Zmod.unsigned (N.v265 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v265 s i)) at 1; unfold R.v265, N.v265.
  rewrite ?node_251.
  rewrite ?node_264.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_266 (s : N.State) (i : N.Inputs) : R.v266 (state s) (inputs i) = Zmod.unsigned (N.v266 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v266 s i)) at 1; unfold R.v266, N.v266.
  rewrite ?node_233.
  rewrite ?node_249.
  rewrite ?node_265.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_267 (s : N.State) (i : N.Inputs) : R.v267 (state s) (inputs i) = Zmod.unsigned (N.v267 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v267 s i)) at 1; unfold R.v267, N.v267.
  rewrite ?node_233.
  rewrite ?node_266.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_268 (s : N.State) (i : N.Inputs) : R.v268 (state s) (inputs i) = Zmod.unsigned (N.v268 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v268 s i)) at 1; unfold R.v268, N.v268.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_269 (s : N.State) (i : N.Inputs) : R.v269 (state s) (inputs i) = Zmod.unsigned (N.v269 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v269 s i)) at 1; unfold R.v269, N.v269.
  unfold R.v70, N.v70.
  rewrite ?node_268.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_270 (s : N.State) (i : N.Inputs) : R.v270 (state s) (inputs i) = Zmod.unsigned (N.v270 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v270 s i)) at 1; unfold R.v270, N.v270.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_271 (s : N.State) (i : N.Inputs) : R.v271 (state s) (inputs i) = Zmod.unsigned (N.v271 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v271 s i)) at 1; unfold R.v271, N.v271.
  unfold R.v73, N.v73.
  rewrite ?node_270.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_272 (s : N.State) (i : N.Inputs) : R.v272 (state s) (inputs i) = Zmod.unsigned (N.v272 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v272 s i)) at 1; unfold R.v272, N.v272.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_273 (s : N.State) (i : N.Inputs) : R.v273 (state s) (inputs i) = Zmod.unsigned (N.v273 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v273 s i)) at 1; unfold R.v273, N.v273.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_274 (s : N.State) (i : N.Inputs) : R.v274 (state s) (inputs i) = Zmod.unsigned (N.v274 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v274 s i)) at 1; unfold R.v274, N.v274.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_275 (s : N.State) (i : N.Inputs) : R.v275 (state s) (inputs i) = Zmod.unsigned (N.v275 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v275 s i)) at 1; unfold R.v275, N.v275.
  unfold R.v26, N.v26.
  rewrite ?node_274.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_276 (s : N.State) (i : N.Inputs) : R.v276 (state s) (inputs i) = Zmod.unsigned (N.v276 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v276 s i)) at 1; unfold R.v276, N.v276.
  unfold R.v78, N.v78.
  rewrite ?node_273.
  rewrite ?node_275.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_277 (s : N.State) (i : N.Inputs) : R.v277 (state s) (inputs i) = Zmod.unsigned (N.v277 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v277 s i)) at 1; unfold R.v277, N.v277.
  unfold R.v76, N.v76.
  rewrite ?node_272.
  rewrite ?node_276.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_278 (s : N.State) (i : N.Inputs) : R.v278 (state s) (inputs i) = Zmod.unsigned (N.v278 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v278 s i)) at 1; unfold R.v278, N.v278.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_279 (s : N.State) (i : N.Inputs) : R.v279 (state s) (inputs i) = Zmod.unsigned (N.v279 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v279 s i)) at 1; unfold R.v279, N.v279.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_280 (s : N.State) (i : N.Inputs) : R.v280 (state s) (inputs i) = Zmod.unsigned (N.v280 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v280 s i)) at 1; unfold R.v280, N.v280.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_281 (s : N.State) (i : N.Inputs) : R.v281 (state s) (inputs i) = Zmod.unsigned (N.v281 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v281 s i)) at 1; unfold R.v281, N.v281.
  unfold R.v26, N.v26.
  rewrite ?node_280.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_282 (s : N.State) (i : N.Inputs) : R.v282 (state s) (inputs i) = Zmod.unsigned (N.v282 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v282 s i)) at 1; unfold R.v282, N.v282.
  unfold R.v78, N.v78.
  rewrite ?node_279.
  rewrite ?node_281.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_283 (s : N.State) (i : N.Inputs) : R.v283 (state s) (inputs i) = Zmod.unsigned (N.v283 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v283 s i)) at 1; unfold R.v283, N.v283.
  unfold R.v76, N.v76.
  rewrite ?node_278.
  rewrite ?node_282.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_284 (s : N.State) (i : N.Inputs) : R.v284 (state s) (inputs i) = Zmod.unsigned (N.v284 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v284 s i)) at 1; unfold R.v284, N.v284.
  rewrite ?node_271.
  rewrite ?node_277.
  rewrite ?node_283.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_285 (s : N.State) (i : N.Inputs) : R.v285 (state s) (inputs i) = Zmod.unsigned (N.v285 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v285 s i)) at 1; unfold R.v285, N.v285.
  rewrite ?node_271.
  rewrite ?node_284.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_286 (s : N.State) (i : N.Inputs) : R.v286 (state s) (inputs i) = Zmod.unsigned (N.v286 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v286 s i)) at 1; unfold R.v286, N.v286.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_287 (s : N.State) (i : N.Inputs) : R.v287 (state s) (inputs i) = Zmod.unsigned (N.v287 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v287 s i)) at 1; unfold R.v287, N.v287.
  unfold R.v73, N.v73.
  rewrite ?node_286.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_288 (s : N.State) (i : N.Inputs) : R.v288 (state s) (inputs i) = Zmod.unsigned (N.v288 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v288 s i)) at 1; unfold R.v288, N.v288.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_289 (s : N.State) (i : N.Inputs) : R.v289 (state s) (inputs i) = Zmod.unsigned (N.v289 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v289 s i)) at 1; unfold R.v289, N.v289.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_290 (s : N.State) (i : N.Inputs) : R.v290 (state s) (inputs i) = Zmod.unsigned (N.v290 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v290 s i)) at 1; unfold R.v290, N.v290.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_291 (s : N.State) (i : N.Inputs) : R.v291 (state s) (inputs i) = Zmod.unsigned (N.v291 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v291 s i)) at 1; unfold R.v291, N.v291.
  unfold R.v26, N.v26.
  rewrite ?node_290.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_292 (s : N.State) (i : N.Inputs) : R.v292 (state s) (inputs i) = Zmod.unsigned (N.v292 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v292 s i)) at 1; unfold R.v292, N.v292.
  unfold R.v78, N.v78.
  rewrite ?node_289.
  rewrite ?node_291.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_293 (s : N.State) (i : N.Inputs) : R.v293 (state s) (inputs i) = Zmod.unsigned (N.v293 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v293 s i)) at 1; unfold R.v293, N.v293.
  unfold R.v76, N.v76.
  rewrite ?node_288.
  rewrite ?node_292.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_294 (s : N.State) (i : N.Inputs) : R.v294 (state s) (inputs i) = Zmod.unsigned (N.v294 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v294 s i)) at 1; unfold R.v294, N.v294.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_295 (s : N.State) (i : N.Inputs) : R.v295 (state s) (inputs i) = Zmod.unsigned (N.v295 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v295 s i)) at 1; unfold R.v295, N.v295.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_296 (s : N.State) (i : N.Inputs) : R.v296 (state s) (inputs i) = Zmod.unsigned (N.v296 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v296 s i)) at 1; unfold R.v296, N.v296.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_297 (s : N.State) (i : N.Inputs) : R.v297 (state s) (inputs i) = Zmod.unsigned (N.v297 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v297 s i)) at 1; unfold R.v297, N.v297.
  unfold R.v26, N.v26.
  rewrite ?node_296.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_298 (s : N.State) (i : N.Inputs) : R.v298 (state s) (inputs i) = Zmod.unsigned (N.v298 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v298 s i)) at 1; unfold R.v298, N.v298.
  unfold R.v78, N.v78.
  rewrite ?node_295.
  rewrite ?node_297.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_299 (s : N.State) (i : N.Inputs) : R.v299 (state s) (inputs i) = Zmod.unsigned (N.v299 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v299 s i)) at 1; unfold R.v299, N.v299.
  unfold R.v76, N.v76.
  rewrite ?node_294.
  rewrite ?node_298.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_300 (s : N.State) (i : N.Inputs) : R.v300 (state s) (inputs i) = Zmod.unsigned (N.v300 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v300 s i)) at 1; unfold R.v300, N.v300.
  rewrite ?node_287.
  rewrite ?node_293.
  rewrite ?node_299.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_301 (s : N.State) (i : N.Inputs) : R.v301 (state s) (inputs i) = Zmod.unsigned (N.v301 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v301 s i)) at 1; unfold R.v301, N.v301.
  rewrite ?node_287.
  rewrite ?node_300.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_302 (s : N.State) (i : N.Inputs) : R.v302 (state s) (inputs i) = Zmod.unsigned (N.v302 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v302 s i)) at 1; unfold R.v302, N.v302.
  rewrite ?node_269.
  rewrite ?node_285.
  rewrite ?node_301.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_303 (s : N.State) (i : N.Inputs) : R.v303 (state s) (inputs i) = Zmod.unsigned (N.v303 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v303 s i)) at 1; unfold R.v303, N.v303.
  rewrite ?node_269.
  rewrite ?node_302.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_304 (s : N.State) (i : N.Inputs) : R.v304 (state s) (inputs i) = Zmod.unsigned (N.v304 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v304 s i)) at 1; unfold R.v304, N.v304.
  rewrite ?node_231.
  rewrite ?node_267.
  rewrite ?node_303.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_305 (s : N.State) (i : N.Inputs) : R.v305 (state s) (inputs i) = Zmod.unsigned (N.v305 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v305 s i)) at 1; unfold R.v305, N.v305.
  rewrite ?node_231.
  rewrite ?node_304.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_306 (s : N.State) (i : N.Inputs) : R.v306 (state s) (inputs i) = Zmod.unsigned (N.v306 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v306 s i)) at 1; unfold R.v306, N.v306.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_307 (s : N.State) (i : N.Inputs) : R.v307 (state s) (inputs i) = Zmod.unsigned (N.v307 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v307 s i)) at 1; unfold R.v307, N.v307.
  unfold R.v67, N.v67.
  rewrite ?node_306.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_308 (s : N.State) (i : N.Inputs) : R.v308 (state s) (inputs i) = Zmod.unsigned (N.v308 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v308 s i)) at 1; unfold R.v308, N.v308.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_309 (s : N.State) (i : N.Inputs) : R.v309 (state s) (inputs i) = Zmod.unsigned (N.v309 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v309 s i)) at 1; unfold R.v309, N.v309.
  unfold R.v70, N.v70.
  rewrite ?node_308.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_310 (s : N.State) (i : N.Inputs) : R.v310 (state s) (inputs i) = Zmod.unsigned (N.v310 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v310 s i)) at 1; unfold R.v310, N.v310.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_311 (s : N.State) (i : N.Inputs) : R.v311 (state s) (inputs i) = Zmod.unsigned (N.v311 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v311 s i)) at 1; unfold R.v311, N.v311.
  unfold R.v73, N.v73.
  rewrite ?node_310.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_312 (s : N.State) (i : N.Inputs) : R.v312 (state s) (inputs i) = Zmod.unsigned (N.v312 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v312 s i)) at 1; unfold R.v312, N.v312.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_313 (s : N.State) (i : N.Inputs) : R.v313 (state s) (inputs i) = Zmod.unsigned (N.v313 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v313 s i)) at 1; unfold R.v313, N.v313.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_314 (s : N.State) (i : N.Inputs) : R.v314 (state s) (inputs i) = Zmod.unsigned (N.v314 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v314 s i)) at 1; unfold R.v314, N.v314.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_315 (s : N.State) (i : N.Inputs) : R.v315 (state s) (inputs i) = Zmod.unsigned (N.v315 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v315 s i)) at 1; unfold R.v315, N.v315.
  unfold R.v26, N.v26.
  rewrite ?node_314.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_316 (s : N.State) (i : N.Inputs) : R.v316 (state s) (inputs i) = Zmod.unsigned (N.v316 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v316 s i)) at 1; unfold R.v316, N.v316.
  unfold R.v78, N.v78.
  rewrite ?node_313.
  rewrite ?node_315.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_317 (s : N.State) (i : N.Inputs) : R.v317 (state s) (inputs i) = Zmod.unsigned (N.v317 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v317 s i)) at 1; unfold R.v317, N.v317.
  unfold R.v76, N.v76.
  rewrite ?node_312.
  rewrite ?node_316.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_318 (s : N.State) (i : N.Inputs) : R.v318 (state s) (inputs i) = Zmod.unsigned (N.v318 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v318 s i)) at 1; unfold R.v318, N.v318.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_319 (s : N.State) (i : N.Inputs) : R.v319 (state s) (inputs i) = Zmod.unsigned (N.v319 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v319 s i)) at 1; unfold R.v319, N.v319.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_320 (s : N.State) (i : N.Inputs) : R.v320 (state s) (inputs i) = Zmod.unsigned (N.v320 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v320 s i)) at 1; unfold R.v320, N.v320.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_321 (s : N.State) (i : N.Inputs) : R.v321 (state s) (inputs i) = Zmod.unsigned (N.v321 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v321 s i)) at 1; unfold R.v321, N.v321.
  unfold R.v26, N.v26.
  rewrite ?node_320.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_322 (s : N.State) (i : N.Inputs) : R.v322 (state s) (inputs i) = Zmod.unsigned (N.v322 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v322 s i)) at 1; unfold R.v322, N.v322.
  unfold R.v78, N.v78.
  rewrite ?node_319.
  rewrite ?node_321.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_323 (s : N.State) (i : N.Inputs) : R.v323 (state s) (inputs i) = Zmod.unsigned (N.v323 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v323 s i)) at 1; unfold R.v323, N.v323.
  unfold R.v76, N.v76.
  rewrite ?node_318.
  rewrite ?node_322.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_324 (s : N.State) (i : N.Inputs) : R.v324 (state s) (inputs i) = Zmod.unsigned (N.v324 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v324 s i)) at 1; unfold R.v324, N.v324.
  rewrite ?node_311.
  rewrite ?node_317.
  rewrite ?node_323.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_325 (s : N.State) (i : N.Inputs) : R.v325 (state s) (inputs i) = Zmod.unsigned (N.v325 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v325 s i)) at 1; unfold R.v325, N.v325.
  rewrite ?node_311.
  rewrite ?node_324.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_326 (s : N.State) (i : N.Inputs) : R.v326 (state s) (inputs i) = Zmod.unsigned (N.v326 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v326 s i)) at 1; unfold R.v326, N.v326.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_327 (s : N.State) (i : N.Inputs) : R.v327 (state s) (inputs i) = Zmod.unsigned (N.v327 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v327 s i)) at 1; unfold R.v327, N.v327.
  unfold R.v73, N.v73.
  rewrite ?node_326.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_328 (s : N.State) (i : N.Inputs) : R.v328 (state s) (inputs i) = Zmod.unsigned (N.v328 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v328 s i)) at 1; unfold R.v328, N.v328.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_329 (s : N.State) (i : N.Inputs) : R.v329 (state s) (inputs i) = Zmod.unsigned (N.v329 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v329 s i)) at 1; unfold R.v329, N.v329.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_330 (s : N.State) (i : N.Inputs) : R.v330 (state s) (inputs i) = Zmod.unsigned (N.v330 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v330 s i)) at 1; unfold R.v330, N.v330.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_331 (s : N.State) (i : N.Inputs) : R.v331 (state s) (inputs i) = Zmod.unsigned (N.v331 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v331 s i)) at 1; unfold R.v331, N.v331.
  unfold R.v26, N.v26.
  rewrite ?node_330.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_332 (s : N.State) (i : N.Inputs) : R.v332 (state s) (inputs i) = Zmod.unsigned (N.v332 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v332 s i)) at 1; unfold R.v332, N.v332.
  unfold R.v78, N.v78.
  rewrite ?node_329.
  rewrite ?node_331.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_333 (s : N.State) (i : N.Inputs) : R.v333 (state s) (inputs i) = Zmod.unsigned (N.v333 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v333 s i)) at 1; unfold R.v333, N.v333.
  unfold R.v76, N.v76.
  rewrite ?node_328.
  rewrite ?node_332.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_334 (s : N.State) (i : N.Inputs) : R.v334 (state s) (inputs i) = Zmod.unsigned (N.v334 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v334 s i)) at 1; unfold R.v334, N.v334.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_335 (s : N.State) (i : N.Inputs) : R.v335 (state s) (inputs i) = Zmod.unsigned (N.v335 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v335 s i)) at 1; unfold R.v335, N.v335.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_336 (s : N.State) (i : N.Inputs) : R.v336 (state s) (inputs i) = Zmod.unsigned (N.v336 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v336 s i)) at 1; unfold R.v336, N.v336.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_337 (s : N.State) (i : N.Inputs) : R.v337 (state s) (inputs i) = Zmod.unsigned (N.v337 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v337 s i)) at 1; unfold R.v337, N.v337.
  unfold R.v26, N.v26.
  rewrite ?node_336.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_338 (s : N.State) (i : N.Inputs) : R.v338 (state s) (inputs i) = Zmod.unsigned (N.v338 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v338 s i)) at 1; unfold R.v338, N.v338.
  unfold R.v78, N.v78.
  rewrite ?node_335.
  rewrite ?node_337.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_339 (s : N.State) (i : N.Inputs) : R.v339 (state s) (inputs i) = Zmod.unsigned (N.v339 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v339 s i)) at 1; unfold R.v339, N.v339.
  unfold R.v76, N.v76.
  rewrite ?node_334.
  rewrite ?node_338.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_340 (s : N.State) (i : N.Inputs) : R.v340 (state s) (inputs i) = Zmod.unsigned (N.v340 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v340 s i)) at 1; unfold R.v340, N.v340.
  rewrite ?node_327.
  rewrite ?node_333.
  rewrite ?node_339.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_341 (s : N.State) (i : N.Inputs) : R.v341 (state s) (inputs i) = Zmod.unsigned (N.v341 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v341 s i)) at 1; unfold R.v341, N.v341.
  rewrite ?node_327.
  rewrite ?node_340.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_342 (s : N.State) (i : N.Inputs) : R.v342 (state s) (inputs i) = Zmod.unsigned (N.v342 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v342 s i)) at 1; unfold R.v342, N.v342.
  rewrite ?node_309.
  rewrite ?node_325.
  rewrite ?node_341.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_343 (s : N.State) (i : N.Inputs) : R.v343 (state s) (inputs i) = Zmod.unsigned (N.v343 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v343 s i)) at 1; unfold R.v343, N.v343.
  rewrite ?node_309.
  rewrite ?node_342.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_344 (s : N.State) (i : N.Inputs) : R.v344 (state s) (inputs i) = Zmod.unsigned (N.v344 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v344 s i)) at 1; unfold R.v344, N.v344.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_345 (s : N.State) (i : N.Inputs) : R.v345 (state s) (inputs i) = Zmod.unsigned (N.v345 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v345 s i)) at 1; unfold R.v345, N.v345.
  unfold R.v70, N.v70.
  rewrite ?node_344.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_346 (s : N.State) (i : N.Inputs) : R.v346 (state s) (inputs i) = Zmod.unsigned (N.v346 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v346 s i)) at 1; unfold R.v346, N.v346.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_347 (s : N.State) (i : N.Inputs) : R.v347 (state s) (inputs i) = Zmod.unsigned (N.v347 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v347 s i)) at 1; unfold R.v347, N.v347.
  unfold R.v73, N.v73.
  rewrite ?node_346.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_348 (s : N.State) (i : N.Inputs) : R.v348 (state s) (inputs i) = Zmod.unsigned (N.v348 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v348 s i)) at 1; unfold R.v348, N.v348.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_349 (s : N.State) (i : N.Inputs) : R.v349 (state s) (inputs i) = Zmod.unsigned (N.v349 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v349 s i)) at 1; unfold R.v349, N.v349.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_350 (s : N.State) (i : N.Inputs) : R.v350 (state s) (inputs i) = Zmod.unsigned (N.v350 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v350 s i)) at 1; unfold R.v350, N.v350.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_351 (s : N.State) (i : N.Inputs) : R.v351 (state s) (inputs i) = Zmod.unsigned (N.v351 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v351 s i)) at 1; unfold R.v351, N.v351.
  unfold R.v26, N.v26.
  rewrite ?node_350.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_352 (s : N.State) (i : N.Inputs) : R.v352 (state s) (inputs i) = Zmod.unsigned (N.v352 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v352 s i)) at 1; unfold R.v352, N.v352.
  unfold R.v78, N.v78.
  rewrite ?node_349.
  rewrite ?node_351.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_353 (s : N.State) (i : N.Inputs) : R.v353 (state s) (inputs i) = Zmod.unsigned (N.v353 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v353 s i)) at 1; unfold R.v353, N.v353.
  unfold R.v76, N.v76.
  rewrite ?node_348.
  rewrite ?node_352.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_354 (s : N.State) (i : N.Inputs) : R.v354 (state s) (inputs i) = Zmod.unsigned (N.v354 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v354 s i)) at 1; unfold R.v354, N.v354.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_355 (s : N.State) (i : N.Inputs) : R.v355 (state s) (inputs i) = Zmod.unsigned (N.v355 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v355 s i)) at 1; unfold R.v355, N.v355.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_356 (s : N.State) (i : N.Inputs) : R.v356 (state s) (inputs i) = Zmod.unsigned (N.v356 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v356 s i)) at 1; unfold R.v356, N.v356.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_357 (s : N.State) (i : N.Inputs) : R.v357 (state s) (inputs i) = Zmod.unsigned (N.v357 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v357 s i)) at 1; unfold R.v357, N.v357.
  unfold R.v26, N.v26.
  rewrite ?node_356.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_358 (s : N.State) (i : N.Inputs) : R.v358 (state s) (inputs i) = Zmod.unsigned (N.v358 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v358 s i)) at 1; unfold R.v358, N.v358.
  unfold R.v78, N.v78.
  rewrite ?node_355.
  rewrite ?node_357.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_359 (s : N.State) (i : N.Inputs) : R.v359 (state s) (inputs i) = Zmod.unsigned (N.v359 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v359 s i)) at 1; unfold R.v359, N.v359.
  unfold R.v76, N.v76.
  rewrite ?node_354.
  rewrite ?node_358.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_360 (s : N.State) (i : N.Inputs) : R.v360 (state s) (inputs i) = Zmod.unsigned (N.v360 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v360 s i)) at 1; unfold R.v360, N.v360.
  rewrite ?node_347.
  rewrite ?node_353.
  rewrite ?node_359.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_361 (s : N.State) (i : N.Inputs) : R.v361 (state s) (inputs i) = Zmod.unsigned (N.v361 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v361 s i)) at 1; unfold R.v361, N.v361.
  rewrite ?node_347.
  rewrite ?node_360.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_362 (s : N.State) (i : N.Inputs) : R.v362 (state s) (inputs i) = Zmod.unsigned (N.v362 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v362 s i)) at 1; unfold R.v362, N.v362.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_363 (s : N.State) (i : N.Inputs) : R.v363 (state s) (inputs i) = Zmod.unsigned (N.v363 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v363 s i)) at 1; unfold R.v363, N.v363.
  unfold R.v73, N.v73.
  rewrite ?node_362.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_364 (s : N.State) (i : N.Inputs) : R.v364 (state s) (inputs i) = Zmod.unsigned (N.v364 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v364 s i)) at 1; unfold R.v364, N.v364.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_365 (s : N.State) (i : N.Inputs) : R.v365 (state s) (inputs i) = Zmod.unsigned (N.v365 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v365 s i)) at 1; unfold R.v365, N.v365.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_366 (s : N.State) (i : N.Inputs) : R.v366 (state s) (inputs i) = Zmod.unsigned (N.v366 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v366 s i)) at 1; unfold R.v366, N.v366.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_367 (s : N.State) (i : N.Inputs) : R.v367 (state s) (inputs i) = Zmod.unsigned (N.v367 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v367 s i)) at 1; unfold R.v367, N.v367.
  unfold R.v26, N.v26.
  rewrite ?node_366.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_368 (s : N.State) (i : N.Inputs) : R.v368 (state s) (inputs i) = Zmod.unsigned (N.v368 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v368 s i)) at 1; unfold R.v368, N.v368.
  unfold R.v78, N.v78.
  rewrite ?node_365.
  rewrite ?node_367.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_369 (s : N.State) (i : N.Inputs) : R.v369 (state s) (inputs i) = Zmod.unsigned (N.v369 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v369 s i)) at 1; unfold R.v369, N.v369.
  unfold R.v76, N.v76.
  rewrite ?node_364.
  rewrite ?node_368.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_370 (s : N.State) (i : N.Inputs) : R.v370 (state s) (inputs i) = Zmod.unsigned (N.v370 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v370 s i)) at 1; unfold R.v370, N.v370.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_371 (s : N.State) (i : N.Inputs) : R.v371 (state s) (inputs i) = Zmod.unsigned (N.v371 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v371 s i)) at 1; unfold R.v371, N.v371.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_372 (s : N.State) (i : N.Inputs) : R.v372 (state s) (inputs i) = Zmod.unsigned (N.v372 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v372 s i)) at 1; unfold R.v372, N.v372.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_373 (s : N.State) (i : N.Inputs) : R.v373 (state s) (inputs i) = Zmod.unsigned (N.v373 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v373 s i)) at 1; unfold R.v373, N.v373.
  unfold R.v26, N.v26.
  rewrite ?node_372.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_374 (s : N.State) (i : N.Inputs) : R.v374 (state s) (inputs i) = Zmod.unsigned (N.v374 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v374 s i)) at 1; unfold R.v374, N.v374.
  unfold R.v78, N.v78.
  rewrite ?node_371.
  rewrite ?node_373.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_375 (s : N.State) (i : N.Inputs) : R.v375 (state s) (inputs i) = Zmod.unsigned (N.v375 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v375 s i)) at 1; unfold R.v375, N.v375.
  unfold R.v76, N.v76.
  rewrite ?node_370.
  rewrite ?node_374.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_376 (s : N.State) (i : N.Inputs) : R.v376 (state s) (inputs i) = Zmod.unsigned (N.v376 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v376 s i)) at 1; unfold R.v376, N.v376.
  rewrite ?node_363.
  rewrite ?node_369.
  rewrite ?node_375.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_377 (s : N.State) (i : N.Inputs) : R.v377 (state s) (inputs i) = Zmod.unsigned (N.v377 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v377 s i)) at 1; unfold R.v377, N.v377.
  rewrite ?node_363.
  rewrite ?node_376.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_378 (s : N.State) (i : N.Inputs) : R.v378 (state s) (inputs i) = Zmod.unsigned (N.v378 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v378 s i)) at 1; unfold R.v378, N.v378.
  rewrite ?node_345.
  rewrite ?node_361.
  rewrite ?node_377.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_379 (s : N.State) (i : N.Inputs) : R.v379 (state s) (inputs i) = Zmod.unsigned (N.v379 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v379 s i)) at 1; unfold R.v379, N.v379.
  rewrite ?node_345.
  rewrite ?node_378.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_380 (s : N.State) (i : N.Inputs) : R.v380 (state s) (inputs i) = Zmod.unsigned (N.v380 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v380 s i)) at 1; unfold R.v380, N.v380.
  rewrite ?node_307.
  rewrite ?node_343.
  rewrite ?node_379.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_381 (s : N.State) (i : N.Inputs) : R.v381 (state s) (inputs i) = Zmod.unsigned (N.v381 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v381 s i)) at 1; unfold R.v381, N.v381.
  rewrite ?node_307.
  rewrite ?node_380.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_382 (s : N.State) (i : N.Inputs) : R.v382 (state s) (inputs i) = Zmod.unsigned (N.v382 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v382 s i)) at 1; unfold R.v382, N.v382.
  rewrite ?node_229.
  rewrite ?node_305.
  rewrite ?node_381.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_383 (s : N.State) (i : N.Inputs) : R.v383 (state s) (inputs i) = Zmod.unsigned (N.v383 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v383 s i)) at 1; unfold R.v383, N.v383.
  rewrite ?node_229.
  rewrite ?node_382.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_384 (s : N.State) (i : N.Inputs) : R.v384 (state s) (inputs i) = Zmod.unsigned (N.v384 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v384 s i)) at 1; unfold R.v384, N.v384.
  unfold R.v62, N.v62.
  rewrite ?node_227.
  rewrite ?node_383.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_385 (s : N.State) (i : N.Inputs) : R.v385 (state s) (inputs i) = Zmod.unsigned (N.v385 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v385 s i)) at 1; unfold R.v385, N.v385.
  rewrite ?node_227.
  rewrite ?node_384.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_386 (s : N.State) (i : N.Inputs) : R.v386 (state s) (inputs i) = Zmod.unsigned (N.v386 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v386 s i)) at 1; unfold R.v386, N.v386.
  rewrite ?node_226.
  rewrite ?node_385.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_387 (s : N.State) (i : N.Inputs) : R.v387 (state s) (inputs i) = Zmod.unsigned (N.v387 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v387 s i)) at 1; unfold R.v387, N.v387.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_388 (s : N.State) (i : N.Inputs) : R.v388 (state s) (inputs i) = Zmod.unsigned (N.v388 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v388 s i)) at 1; unfold R.v388, N.v388.
  rewrite ?node_386.
  unfold R.v387, N.v387.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_389 (s : N.State) (i : N.Inputs) : R.v389 (state s) (inputs i) = Zmod.unsigned (N.v389 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v389 s i)) at 1; unfold R.v389, N.v389.
  rewrite ?node_386.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_390 (s : N.State) (i : N.Inputs) : R.v390 (state s) (inputs i) = Zmod.unsigned (N.v390 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v390 s i)) at 1; unfold R.v390, N.v390.
  unfold R.v9, N.v9.
  rewrite ?node_388.
  rewrite ?node_389.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_391 (s : N.State) (i : N.Inputs) : R.v391 (state s) (inputs i) = Zmod.unsigned (N.v391 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v391 s i)) at 1; unfold R.v391, N.v391.
  unfold R.v62, N.v62.
  rewrite ?node_390.
  rewrite !state_r1_ndivBy0Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r1_ndivBy0Reg s)).
  finish_numeric.
Qed.
Lemma node_392 (s : N.State) (i : N.Inputs) : R.v392 (state s) (inputs i) = Zmod.unsigned (N.v392 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v392 s i)) at 1; unfold R.v392, N.v392.
  rewrite ?node_8.
  unfold R.v22, N.v22.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_393 (s : N.State) (i : N.Inputs) : R.v393 (state s) (inputs i) = Zmod.unsigned (N.v393 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v393 s i)) at 1; unfold R.v393, N.v393.
  rewrite ?node_6.
  rewrite ?node_392.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_394 (s : N.State) (i : N.Inputs) : R.v394 (state s) (inputs i) = Zmod.unsigned (N.v394 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v394 s i)) at 1; unfold R.v394, N.v394.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_395 (s : N.State) (i : N.Inputs) : R.v395 (state s) (inputs i) = Zmod.unsigned (N.v395 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v395 s i)) at 1; unfold R.v395, N.v395.
  unfold R.v394, N.v394.
  rewrite !state_r9_ncnt_5Fvalue.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r9_ncnt_5Fvalue s)).
  finish_numeric.
Qed.
Lemma node_396 (s : N.State) (i : N.Inputs) : R.v396 (state s) (inputs i) = Zmod.unsigned (N.v396 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v396 s i)) at 1; unfold R.v396, N.v396.
  rewrite ?node_393.
  rewrite ?node_395.
  rewrite !state_r9_ncnt_5Fvalue.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r9_ncnt_5Fvalue s)).
  finish_numeric.
Qed.
Lemma node_397 (s : N.State) (i : N.Inputs) : R.v397 (state s) (inputs i) = Zmod.unsigned (N.v397 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v397 s i)) at 1; unfold R.v397, N.v397.
  rewrite ?node_4.
  rewrite ?node_391.
  rewrite ?node_396.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_398 (s : N.State) (i : N.Inputs) : R.v398 (state s) (inputs i) = Zmod.unsigned (N.v398 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v398 s i)) at 1; unfold R.v398, N.v398.
  rewrite ?node_2.
  rewrite ?node_397.
  rewrite !state_r9_ncnt_5Fvalue.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r9_ncnt_5Fvalue s)).
  finish_numeric.
Qed.
Lemma node_399 (s : N.State) (i : N.Inputs) : R.v399 (state s) (inputs i) = Zmod.unsigned (N.v399 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v399 s i)) at 1; unfold R.v399, N.v399.
  unfold R.v11, N.v11.
  rewrite !state_r0_nstate.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r0_nstate s)).
  finish_numeric.
Qed.
Lemma node_400 (s : N.State) (i : N.Inputs) : R.v400 (state s) (inputs i) = Zmod.unsigned (N.v400 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v400 s i)) at 1; unfold R.v400, N.v400.
  unfold R.v22, N.v22.
  rewrite !inputs_nio_5Fout_5Fready.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fout_5Fready i)).
  finish_numeric.
Qed.
Lemma node_401 (s : N.State) (i : N.Inputs) : R.v401 (state s) (inputs i) = Zmod.unsigned (N.v401 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v401 s i)) at 1; unfold R.v401, N.v401.
  rewrite ?node_399.
  rewrite ?node_400.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_402 (s : N.State) (i : N.Inputs) : R.v402 (state s) (inputs i) = Zmod.unsigned (N.v402 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v402 s i)) at 1; unfold R.v402, N.v402.
  rewrite !state_r2_nshiftReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r2_nshiftReg s)).
  finish_numeric.
Qed.
Lemma node_403 (s : N.State) (i : N.Inputs) : R.v403 (state s) (inputs i) = Zmod.unsigned (N.v403 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v403 s i)) at 1; unfold R.v403, N.v403.
  unfold R.v20, N.v20.
  rewrite ?node_402.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_404 (s : N.State) (i : N.Inputs) : R.v404 (state s) (inputs i) = Zmod.unsigned (N.v404 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v404 s i)) at 1; unfold R.v404, N.v404.
  rewrite ?node_402.
  rewrite ?node_403.
  rewrite !state_r3_naSignReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r3_naSignReg s)).
  finish_numeric.
Qed.
Lemma node_405 (s : N.State) (i : N.Inputs) : R.v405 (state s) (inputs i) = Zmod.unsigned (N.v405 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v405 s i)) at 1; unfold R.v405, N.v405.
  unfold R.v20, N.v20.
  rewrite ?node_40.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_406 (s : N.State) (i : N.Inputs) : R.v406 (state s) (inputs i) = Zmod.unsigned (N.v406 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v406 s i)) at 1; unfold R.v406, N.v406.
  rewrite ?node_40.
  rewrite ?node_405.
  rewrite !state_r4_nqSignReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r4_nqSignReg s)).
  finish_numeric.
Qed.
Lemma node_407 (s : N.State) (i : N.Inputs) : R.v407 (state s) (inputs i) = Zmod.unsigned (N.v407 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v407 s i)) at 1; unfold R.v407, N.v407.
  rewrite ?node_404.
  rewrite ?node_406.
  rewrite !state_r8_nctrlReg_5FisHi.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r8_nctrlReg_5FisHi s)).
  finish_numeric.
Qed.
Lemma node_408 (s : N.State) (i : N.Inputs) : R.v408 (state s) (inputs i) = Zmod.unsigned (N.v408 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v408 s i)) at 1; unfold R.v408, N.v408.
  rewrite ?node_407.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_409 (s : N.State) (i : N.Inputs) : R.v409 (state s) (inputs i) = Zmod.unsigned (N.v409 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v409 s i)) at 1; unfold R.v409, N.v409.
  rewrite ?node_408.
  unfold RB.word.
  rewrite repeat_32, bits.mod_to_Z; reflexivity.
Qed.
Lemma node_410 (s : N.State) (i : N.Inputs) : R.v410 (state s) (inputs i) = Zmod.unsigned (N.v410 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v410 s i)) at 1; unfold R.v410, N.v410.
  rewrite ?node_407.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_411 (s : N.State) (i : N.Inputs) : R.v411 (state s) (inputs i) = Zmod.unsigned (N.v411 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v411 s i)) at 1; unfold R.v411, N.v411.
  rewrite ?node_409.
  rewrite ?node_410.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_412 (s : N.State) (i : N.Inputs) : R.v412 (state s) (inputs i) = Zmod.unsigned (N.v412 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v412 s i)) at 1; unfold R.v412, N.v412.
  rewrite ?node_407.
  rewrite ?node_411.
  rewrite !state_r7_nctrlReg_5FisW.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r7_nctrlReg_5FisW s)).
  finish_numeric.
Qed.
Lemma node_413 (s : N.State) (i : N.Inputs) : R.v413 (state s) (inputs i) = Zmod.unsigned (N.v413 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v413 s i)) at 1; unfold R.v413, N.v413.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_414 (s : N.State) (i : N.Inputs) : R.v414 (state s) (inputs i) = Zmod.unsigned (N.v414 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v414 s i)) at 1; unfold R.v414, N.v414.
  rewrite ?node_40.
  unfold R.v413, N.v413.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_415 (s : N.State) (i : N.Inputs) : R.v415 (state s) (inputs i) = Zmod.unsigned (N.v415 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v415 s i)) at 1; unfold R.v415, N.v415.
  unfold R.v22, N.v22.
  rewrite !inputs_nreset.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  finish_numeric.
Qed.
Lemma node_416 (s : N.State) (i : N.Inputs) : R.v416 (state s) (inputs i) = Zmod.unsigned (N.v416 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v416 s i)) at 1; unfold R.v416, N.v416.
  rewrite ?node_399.
  rewrite ?node_415.
  rewrite !state_r1_ndivBy0Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r1_ndivBy0Reg s)).
  finish_numeric.
Qed.
Lemma node_417 (s : N.State) (i : N.Inputs) : R.v417 (state s) (inputs i) = Zmod.unsigned (N.v417 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v417 s i)) at 1; unfold R.v417, N.v417.
  rewrite !state_r6_naValx2Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r6_naValx2Reg s)).
  finish_numeric.
Qed.
Lemma node_418 (s : N.State) (i : N.Inputs) : R.v418 (state s) (inputs i) = Zmod.unsigned (N.v418 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v418 s i)) at 1; unfold R.v418, N.v418.
  rewrite ?node_402.
  rewrite ?node_417.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_419 (s : N.State) (i : N.Inputs) : R.v419 (state s) (inputs i) = Zmod.unsigned (N.v419 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v419 s i)) at 1; unfold R.v419, N.v419.
  unfold R.v20, N.v20.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_420 (s : N.State) (i : N.Inputs) : R.v420 (state s) (inputs i) = Zmod.unsigned (N.v420 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v420 s i)) at 1; unfold R.v420, N.v420.
  unfold R.v22, N.v22.
  rewrite !state_r1_ndivBy0Reg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r1_ndivBy0Reg s)).
  finish_numeric.
Qed.
Lemma node_421 (s : N.State) (i : N.Inputs) : R.v421 (state s) (inputs i) = Zmod.unsigned (N.v421 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v421 s i)) at 1; unfold R.v421, N.v421.
  rewrite ?node_399.
  rewrite ?node_415.
  rewrite ?node_420.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_422 (s : N.State) (i : N.Inputs) : R.v422 (state s) (inputs i) = Zmod.unsigned (N.v422 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v422 s i)) at 1; unfold R.v422, N.v422.
  unfold R.v20, N.v20.
  rewrite ?node_40.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_423 (s : N.State) (i : N.Inputs) : R.v423 (state s) (inputs i) = Zmod.unsigned (N.v423 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v423 s i)) at 1; unfold R.v423, N.v423.
  unfold R.v20, N.v20.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_424 (s : N.State) (i : N.Inputs) : R.v424 (state s) (inputs i) = Zmod.unsigned (N.v424 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v424 s i)) at 1; unfold R.v424, N.v424.
  rewrite ?node_422.
  rewrite ?node_423.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_425 (s : N.State) (i : N.Inputs) : R.v425 (state s) (inputs i) = Zmod.unsigned (N.v425 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v425 s i)) at 1; unfold R.v425, N.v425.
  unfold R.v26, N.v26.
  rewrite ?node_424.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_426 (s : N.State) (i : N.Inputs) : R.v426 (state s) (inputs i) = Zmod.unsigned (N.v426 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v426 s i)) at 1; unfold R.v426, N.v426.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_427 (s : N.State) (i : N.Inputs) : R.v427 (state s) (inputs i) = Zmod.unsigned (N.v427 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v427 s i)) at 1; unfold R.v427, N.v427.
  rewrite ?node_402.
  unfold R.v426, N.v426.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_428 (s : N.State) (i : N.Inputs) : R.v428 (state s) (inputs i) = Zmod.unsigned (N.v428 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v428 s i)) at 1; unfold R.v428, N.v428.
  rewrite ?node_425.
  rewrite ?node_427.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_429 (s : N.State) (i : N.Inputs) : R.v429 (state s) (inputs i) = Zmod.unsigned (N.v429 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v429 s i)) at 1; unfold R.v429, N.v429.
  rewrite ?node_417.
  unfold R.v426, N.v426.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_430 (s : N.State) (i : N.Inputs) : R.v430 (state s) (inputs i) = Zmod.unsigned (N.v430 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v430 s i)) at 1; unfold R.v430, N.v430.
  rewrite ?node_428.
  rewrite ?node_429.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_431 (s : N.State) (i : N.Inputs) : R.v431 (state s) (inputs i) = Zmod.unsigned (N.v431 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v431 s i)) at 1; unfold R.v431, N.v431.
  rewrite ?node_402.
  rewrite !state_r5_nbReg.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r5_nbReg s)).
  finish_numeric.
Qed.
Lemma node_432 (s : N.State) (i : N.Inputs) : R.v432 (state s) (inputs i) = Zmod.unsigned (N.v432 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v432 s i)) at 1; unfold R.v432, N.v432.
  unfold R.v3, N.v3.
  rewrite !state_r11_npreviousState.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r11_npreviousState s)).
  finish_numeric.
Qed.
Lemma node_433 (s : N.State) (i : N.Inputs) : R.v433 (state s) (inputs i) = Zmod.unsigned (N.v433 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v433 s i)) at 1; unfold R.v433, N.v433.
  rewrite ?node_415.
  rewrite ?node_432.
  rewrite !state_r10_nhistoryValid.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r10_nhistoryValid s)).
  finish_numeric.
Qed.
Lemma node_434 (s : N.State) (i : N.Inputs) : R.v434 (state s) (inputs i) = Zmod.unsigned (N.v434 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v434 s i)) at 1; unfold R.v434, N.v434.
  unfold R.v5, N.v5.
  rewrite !state_r11_npreviousState.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r11_npreviousState s)).
  finish_numeric.
Qed.
Lemma node_435 (s : N.State) (i : N.Inputs) : R.v435 (state s) (inputs i) = Zmod.unsigned (N.v435 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v435 s i)) at 1; unfold R.v435, N.v435.
  rewrite ?node_415.
  rewrite ?node_434.
  rewrite !state_r10_nhistoryValid.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r10_nhistoryValid s)).
  finish_numeric.
Qed.
Lemma node_436 (s : N.State) (i : N.Inputs) : R.v436 (state s) (inputs i) = Zmod.unsigned (N.v436 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v436 s i)) at 1; unfold R.v436, N.v436.
  unfold R.v9, N.v9.
  rewrite !state_r12_npreviousCount.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r12_npreviousCount s)).
  finish_numeric.
Qed.
Lemma node_437 (s : N.State) (i : N.Inputs) : R.v437 (state s) (inputs i) = Zmod.unsigned (N.v437 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v437 s i)) at 1; unfold R.v437, N.v437.
  unfold R.v7, N.v7.
  unfold R.v11, N.v11.
  rewrite ?node_436.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_438 (s : N.State) (i : N.Inputs) : R.v438 (state s) (inputs i) = Zmod.unsigned (N.v438 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v438 s i)) at 1; unfold R.v438, N.v438.
  rewrite ?node_437.
  rewrite !state_r0_nstate.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r0_nstate s)).
  finish_numeric.
Qed.
Lemma node_439 (s : N.State) (i : N.Inputs) : R.v439 (state s) (inputs i) = Zmod.unsigned (N.v439 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v439 s i)) at 1; unfold R.v439, N.v439.
  unfold R.v7, N.v7.
  rewrite !state_r11_npreviousState.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r11_npreviousState s)).
  finish_numeric.
Qed.
Lemma node_440 (s : N.State) (i : N.Inputs) : R.v440 (state s) (inputs i) = Zmod.unsigned (N.v440 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v440 s i)) at 1; unfold R.v440, N.v440.
  rewrite ?node_415.
  rewrite ?node_439.
  rewrite !state_r10_nhistoryValid.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r10_nhistoryValid s)).
  finish_numeric.
Qed.
Lemma node_441 (s : N.State) (i : N.Inputs) : R.v441 (state s) (inputs i) = Zmod.unsigned (N.v441 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v441 s i)) at 1; unfold R.v441, N.v441.
  unfold R.v394, N.v394.
  rewrite !state_r12_npreviousCount.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r12_npreviousCount s)).
  finish_numeric.
Qed.
Lemma node_442 (s : N.State) (i : N.Inputs) : R.v442 (state s) (inputs i) = Zmod.unsigned (N.v442 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v442 s i)) at 1; unfold R.v442, N.v442.
  unfold R.v62, N.v62.
  rewrite ?node_436.
  rewrite ?node_441.
  unfold RB.word.
  finish_numeric.
Qed.
Lemma node_443 (s : N.State) (i : N.Inputs) : R.v443 (state s) (inputs i) = Zmod.unsigned (N.v443 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v443 s i)) at 1; unfold R.v443, N.v443.
  rewrite ?node_442.
  rewrite !state_r9_ncnt_5Fvalue.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r9_ncnt_5Fvalue s)).
  finish_numeric.
Qed.
Lemma node_444 (s : N.State) (i : N.Inputs) : R.v444 (state s) (inputs i) = Zmod.unsigned (N.v444 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v444 s i)) at 1; unfold R.v444, N.v444.
  rewrite ?node_415.
  rewrite !state_r13_nwasStalled.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r13_nwasStalled s)).
  finish_numeric.
Qed.
Lemma node_445 (s : N.State) (i : N.Inputs) : R.v445 (state s) (inputs i) = Zmod.unsigned (N.v445 s i).
Proof. rewrite <- (bits.mod_to_Z (N.v445 s i)) at 1; unfold R.v445, N.v445.
  rewrite ?node_412.
  rewrite !state_r14_npreviousOutput.
  unfold RB.word.
  rewrite ?(bits.mod_to_Z (N.r14_npreviousOutput s)).
  finish_numeric.
Qed.
Lemma state_ext (a b : R.State) :
  R.r0_nstate a = R.r0_nstate b ->
  R.r1_ndivBy0Reg a = R.r1_ndivBy0Reg b ->
  R.r2_nshiftReg a = R.r2_nshiftReg b ->
  R.r3_naSignReg a = R.r3_naSignReg b ->
  R.r4_nqSignReg a = R.r4_nqSignReg b ->
  R.r5_nbReg a = R.r5_nbReg b ->
  R.r6_naValx2Reg a = R.r6_naValx2Reg b ->
  R.r7_nctrlReg_5FisW a = R.r7_nctrlReg_5FisW b ->
  R.r8_nctrlReg_5FisHi a = R.r8_nctrlReg_5FisHi b ->
  R.r9_ncnt_5Fvalue a = R.r9_ncnt_5Fvalue b ->
  R.r10_nhistoryValid a = R.r10_nhistoryValid b ->
  R.r11_npreviousState a = R.r11_npreviousState b ->
  R.r12_npreviousCount a = R.r12_npreviousCount b ->
  R.r13_nwasStalled a = R.r13_nwasStalled b ->
  R.r14_npreviousOutput a = R.r14_npreviousOutput b ->
  a = b.
Proof. destruct a, b; cbn; intros; subst; reflexivity. Qed.
Lemma outputs_ext (a b : R.Outputs) :
  R.nio_5Fin_5Fready a = R.nio_5Fin_5Fready b ->
  R.nio_5Fout_5Fvalid a = R.nio_5Fout_5Fvalid b ->
  R.nio_5Fout_5Fbits_5Fdata a = R.nio_5Fout_5Fbits_5Fdata b ->
  a = b.
Proof. destruct a, b; cbn; intros; subst; reflexivity. Qed.
Theorem step_refines (s : N.State) (i : N.Inputs) : state (N.step s i) = R.step (state s) (inputs i).
Proof. apply state_ext.
  - rewrite state_r0_nstate.
    change (Zmod.unsigned (if Zmod.eqb (N.nreset i) Zmod.one then N.v0 s i else N.v19 s i) =
      if Z.eqb (Zmod.unsigned (N.nreset i) mod 2^1) 1 then R.v0 (state s) (inputs i) else R.v19 (state s) (inputs i)).
    rewrite bits.mod_to_Z, node_0, node_19; finish_numeric.
  - rewrite state_r1_ndivBy0Reg.
    change (Zmod.unsigned (N.v24 s i) = R.v24 (state s) (inputs i)); symmetry; exact (node_24 s i).
  - rewrite state_r2_nshiftReg.
    change (Zmod.unsigned (N.v44 s i) = R.v44 (state s) (inputs i)); symmetry; exact (node_44 s i).
  - rewrite state_r3_naSignReg.
    change (Zmod.unsigned (N.v47 s i) = R.v47 (state s) (inputs i)); symmetry; exact (node_47 s i).
  - rewrite state_r4_nqSignReg.
    change (Zmod.unsigned (N.v52 s i) = R.v52 (state s) (inputs i)); symmetry; exact (node_52 s i).
  - rewrite state_r5_nbReg.
    change (Zmod.unsigned (N.v55 s i) = R.v55 (state s) (inputs i)); symmetry; exact (node_55 s i).
  - rewrite state_r6_naValx2Reg.
    change (Zmod.unsigned (N.v59 s i) = R.v59 (state s) (inputs i)); symmetry; exact (node_59 s i).
  - rewrite state_r7_nctrlReg_5FisW.
    change (Zmod.unsigned (N.v60 s i) = R.v60 (state s) (inputs i)); symmetry; exact (node_60 s i).
  - rewrite state_r8_nctrlReg_5FisHi.
    change (Zmod.unsigned (N.v61 s i) = R.v61 (state s) (inputs i)); symmetry; exact (node_61 s i).
  - rewrite state_r9_ncnt_5Fvalue.
    change (Zmod.unsigned (if Zmod.eqb (N.nreset i) Zmod.one then N.v62 s i else N.v398 s i) =
      if Z.eqb (Zmod.unsigned (N.nreset i) mod 2^1) 1 then R.v62 (state s) (inputs i) else R.v398 (state s) (inputs i)).
    rewrite bits.mod_to_Z, node_62, node_398; finish_numeric.
  - rewrite state_r10_nhistoryValid.
    change (Zmod.unsigned (if Zmod.eqb (N.nreset i) Zmod.one then N.v26 s i else N.v22 s i) =
      if Z.eqb (Zmod.unsigned (N.nreset i) mod 2^1) 1 then R.v26 (state s) (inputs i) else R.v22 (state s) (inputs i)).
    rewrite bits.mod_to_Z, node_26, node_22; finish_numeric.
  - rewrite state_r11_npreviousState.
    change (Zmod.unsigned (N.r0_nstate s) = RB.word 3 (R.r0_nstate (state s))).
    rewrite state_r0_nstate; unfold RB.word; symmetry; apply bits.mod_to_Z.
  - rewrite state_r12_npreviousCount.
    change (Zmod.unsigned (N.r9_ncnt_5Fvalue s) = RB.word 6 (R.r9_ncnt_5Fvalue (state s))).
    rewrite state_r9_ncnt_5Fvalue; unfold RB.word; symmetry; apply bits.mod_to_Z.
  - rewrite state_r13_nwasStalled.
    change (Zmod.unsigned (if Zmod.eqb (N.nreset i) Zmod.one then N.v26 s i else N.v401 s i) =
      if Z.eqb (Zmod.unsigned (N.nreset i) mod 2^1) 1 then R.v26 (state s) (inputs i) else R.v401 (state s) (inputs i)).
    rewrite bits.mod_to_Z, node_26, node_401; finish_numeric.
  - rewrite state_r14_npreviousOutput.
    change (Zmod.unsigned (N.v412 s i) = R.v412 (state s) (inputs i)); symmetry; exact (node_412 s i).
Qed.
Theorem run_refines (s : N.State) (pins : nat -> N.Inputs) t : state (N.run s pins t) = R.run (state s) (fun k => inputs (pins k)) t.
Proof. induction t; cbn [N.run R.run]; [reflexivity | rewrite step_refines, IHt; reflexivity]. Qed.
Lemma output_nio_5Fin_5Fready s i : R.nio_5Fin_5Fready (R.observe (state s) (inputs i)) = Zmod.unsigned (N.nio_5Fin_5Fready (N.observe s i)).
Proof.
  exact (node_1 s i).
Qed.
Lemma output_nio_5Fout_5Fvalid s i : R.nio_5Fout_5Fvalid (R.observe (state s) (inputs i)) = Zmod.unsigned (N.nio_5Fout_5Fvalid (N.observe s i)).
Proof.
  exact (node_399 s i).
Qed.
Lemma output_nio_5Fout_5Fbits_5Fdata s i : R.nio_5Fout_5Fbits_5Fdata (R.observe (state s) (inputs i)) = Zmod.unsigned (N.nio_5Fout_5Fbits_5Fdata (N.observe s i)).
Proof.
  exact (node_412 s i).
Qed.
Theorem observe_refines s i : outputs (N.observe s i) = R.observe (state s) (inputs i).
Proof. apply outputs_ext.
  - rewrite outputs_nio_5Fin_5Fready; symmetry; apply output_nio_5Fin_5Fready.
  - rewrite outputs_nio_5Fout_5Fvalid; symmetry; apply output_nio_5Fout_5Fvalid.
  - rewrite outputs_nio_5Fout_5Fbits_5Fdata; symmetry; apply output_nio_5Fout_5Fbits_5Fdata.
Qed.
Local Opaque R.v0 N.v0 R.v1 N.v1 R.v2 N.v2 R.v3 N.v3 R.v4 N.v4 R.v5 N.v5 R.v6 N.v6 R.v7 N.v7 R.v8 N.v8 R.v9 N.v9 R.v10 N.v10 R.v11 N.v11 R.v12 N.v12 R.v13 N.v13 R.v14 N.v14 R.v15 N.v15 R.v16 N.v16 R.v17 N.v17 R.v18 N.v18 R.v19 N.v19 R.v20 N.v20 R.v21 N.v21 R.v22 N.v22 R.v23 N.v23 R.v24 N.v24 R.v25 N.v25 R.v26 N.v26 R.v27 N.v27 R.v28 N.v28 R.v29 N.v29 R.v30 N.v30 R.v31 N.v31 R.v32 N.v32 R.v33 N.v33 R.v34 N.v34 R.v35 N.v35 R.v36 N.v36 R.v37 N.v37 R.v38 N.v38 R.v39 N.v39 R.v40 N.v40 R.v41 N.v41 R.v42 N.v42 R.v43 N.v43 R.v44 N.v44 R.v45 N.v45 R.v46 N.v46 R.v47 N.v47 R.v48 N.v48 R.v49 N.v49 R.v50 N.v50 R.v51 N.v51 R.v52 N.v52 R.v53 N.v53 R.v54 N.v54 R.v55 N.v55 R.v56 N.v56 R.v57 N.v57 R.v58 N.v58 R.v59 N.v59 R.v60 N.v60 R.v61 N.v61 R.v62 N.v62 R.v63 N.v63 R.v64 N.v64 R.v65 N.v65 R.v66 N.v66 R.v67 N.v67 R.v68 N.v68 R.v69 N.v69 R.v70 N.v70 R.v71 N.v71 R.v72 N.v72 R.v73 N.v73 R.v74 N.v74 R.v75 N.v75 R.v76 N.v76 R.v77 N.v77 R.v78 N.v78 R.v79 N.v79 R.v80 N.v80 R.v81 N.v81 R.v82 N.v82 R.v83 N.v83 R.v84 N.v84 R.v85 N.v85 R.v86 N.v86 R.v87 N.v87 R.v88 N.v88 R.v89 N.v89 R.v90 N.v90 R.v91 N.v91 R.v92 N.v92 R.v93 N.v93 R.v94 N.v94 R.v95 N.v95 R.v96 N.v96 R.v97 N.v97 R.v98 N.v98 R.v99 N.v99 R.v100 N.v100 R.v101 N.v101 R.v102 N.v102 R.v103 N.v103 R.v104 N.v104 R.v105 N.v105 R.v106 N.v106 R.v107 N.v107 R.v108 N.v108 R.v109 N.v109 R.v110 N.v110 R.v111 N.v111 R.v112 N.v112 R.v113 N.v113 R.v114 N.v114 R.v115 N.v115 R.v116 N.v116 R.v117 N.v117 R.v118 N.v118 R.v119 N.v119 R.v120 N.v120 R.v121 N.v121 R.v122 N.v122 R.v123 N.v123 R.v124 N.v124 R.v125 N.v125 R.v126 N.v126 R.v127 N.v127 R.v128 N.v128 R.v129 N.v129 R.v130 N.v130 R.v131 N.v131 R.v132 N.v132 R.v133 N.v133 R.v134 N.v134 R.v135 N.v135 R.v136 N.v136 R.v137 N.v137 R.v138 N.v138 R.v139 N.v139 R.v140 N.v140 R.v141 N.v141 R.v142 N.v142 R.v143 N.v143 R.v144 N.v144 R.v145 N.v145 R.v146 N.v146 R.v147 N.v147 R.v148 N.v148 R.v149 N.v149 R.v150 N.v150 R.v151 N.v151 R.v152 N.v152 R.v153 N.v153 R.v154 N.v154 R.v155 N.v155 R.v156 N.v156 R.v157 N.v157 R.v158 N.v158 R.v159 N.v159 R.v160 N.v160 R.v161 N.v161 R.v162 N.v162 R.v163 N.v163 R.v164 N.v164 R.v165 N.v165 R.v166 N.v166 R.v167 N.v167 R.v168 N.v168 R.v169 N.v169 R.v170 N.v170 R.v171 N.v171 R.v172 N.v172 R.v173 N.v173 R.v174 N.v174 R.v175 N.v175 R.v176 N.v176 R.v177 N.v177 R.v178 N.v178 R.v179 N.v179 R.v180 N.v180 R.v181 N.v181 R.v182 N.v182 R.v183 N.v183 R.v184 N.v184 R.v185 N.v185 R.v186 N.v186 R.v187 N.v187 R.v188 N.v188 R.v189 N.v189 R.v190 N.v190 R.v191 N.v191 R.v192 N.v192 R.v193 N.v193 R.v194 N.v194 R.v195 N.v195 R.v196 N.v196 R.v197 N.v197 R.v198 N.v198 R.v199 N.v199 R.v200 N.v200 R.v201 N.v201 R.v202 N.v202 R.v203 N.v203 R.v204 N.v204 R.v205 N.v205 R.v206 N.v206 R.v207 N.v207 R.v208 N.v208 R.v209 N.v209 R.v210 N.v210 R.v211 N.v211 R.v212 N.v212 R.v213 N.v213 R.v214 N.v214 R.v215 N.v215 R.v216 N.v216 R.v217 N.v217 R.v218 N.v218 R.v219 N.v219 R.v220 N.v220 R.v221 N.v221 R.v222 N.v222 R.v223 N.v223 R.v224 N.v224 R.v225 N.v225 R.v226 N.v226 R.v227 N.v227 R.v228 N.v228 R.v229 N.v229 R.v230 N.v230 R.v231 N.v231 R.v232 N.v232 R.v233 N.v233 R.v234 N.v234 R.v235 N.v235 R.v236 N.v236 R.v237 N.v237 R.v238 N.v238 R.v239 N.v239 R.v240 N.v240 R.v241 N.v241 R.v242 N.v242 R.v243 N.v243 R.v244 N.v244 R.v245 N.v245 R.v246 N.v246 R.v247 N.v247 R.v248 N.v248 R.v249 N.v249 R.v250 N.v250 R.v251 N.v251 R.v252 N.v252 R.v253 N.v253 R.v254 N.v254 R.v255 N.v255 R.v256 N.v256 R.v257 N.v257 R.v258 N.v258 R.v259 N.v259 R.v260 N.v260 R.v261 N.v261 R.v262 N.v262 R.v263 N.v263 R.v264 N.v264 R.v265 N.v265 R.v266 N.v266 R.v267 N.v267 R.v268 N.v268 R.v269 N.v269 R.v270 N.v270 R.v271 N.v271 R.v272 N.v272 R.v273 N.v273 R.v274 N.v274 R.v275 N.v275 R.v276 N.v276 R.v277 N.v277 R.v278 N.v278 R.v279 N.v279 R.v280 N.v280 R.v281 N.v281 R.v282 N.v282 R.v283 N.v283 R.v284 N.v284 R.v285 N.v285 R.v286 N.v286 R.v287 N.v287 R.v288 N.v288 R.v289 N.v289 R.v290 N.v290 R.v291 N.v291 R.v292 N.v292 R.v293 N.v293 R.v294 N.v294 R.v295 N.v295 R.v296 N.v296 R.v297 N.v297 R.v298 N.v298 R.v299 N.v299 R.v300 N.v300 R.v301 N.v301 R.v302 N.v302 R.v303 N.v303 R.v304 N.v304 R.v305 N.v305 R.v306 N.v306 R.v307 N.v307 R.v308 N.v308 R.v309 N.v309 R.v310 N.v310 R.v311 N.v311 R.v312 N.v312 R.v313 N.v313 R.v314 N.v314 R.v315 N.v315 R.v316 N.v316 R.v317 N.v317 R.v318 N.v318 R.v319 N.v319 R.v320 N.v320 R.v321 N.v321 R.v322 N.v322 R.v323 N.v323 R.v324 N.v324 R.v325 N.v325 R.v326 N.v326 R.v327 N.v327 R.v328 N.v328 R.v329 N.v329 R.v330 N.v330 R.v331 N.v331 R.v332 N.v332 R.v333 N.v333 R.v334 N.v334 R.v335 N.v335 R.v336 N.v336 R.v337 N.v337 R.v338 N.v338 R.v339 N.v339 R.v340 N.v340 R.v341 N.v341 R.v342 N.v342 R.v343 N.v343 R.v344 N.v344 R.v345 N.v345 R.v346 N.v346 R.v347 N.v347 R.v348 N.v348 R.v349 N.v349 R.v350 N.v350 R.v351 N.v351 R.v352 N.v352 R.v353 N.v353 R.v354 N.v354 R.v355 N.v355 R.v356 N.v356 R.v357 N.v357 R.v358 N.v358 R.v359 N.v359 R.v360 N.v360 R.v361 N.v361 R.v362 N.v362 R.v363 N.v363 R.v364 N.v364 R.v365 N.v365 R.v366 N.v366 R.v367 N.v367 R.v368 N.v368 R.v369 N.v369 R.v370 N.v370 R.v371 N.v371 R.v372 N.v372 R.v373 N.v373 R.v374 N.v374 R.v375 N.v375 R.v376 N.v376 R.v377 N.v377 R.v378 N.v378 R.v379 N.v379 R.v380 N.v380 R.v381 N.v381 R.v382 N.v382 R.v383 N.v383 R.v384 N.v384 R.v385 N.v385 R.v386 N.v386 R.v387 N.v387 R.v388 N.v388 R.v389 N.v389 R.v390 N.v390 R.v391 N.v391 R.v392 N.v392 R.v393 N.v393 R.v394 N.v394 R.v395 N.v395 R.v396 N.v396 R.v397 N.v397 R.v398 N.v398 R.v399 N.v399 R.v400 N.v400 R.v401 N.v401 R.v402 N.v402 R.v403 N.v403 R.v404 N.v404 R.v405 N.v405 R.v406 N.v406 R.v407 N.v407 R.v408 N.v408 R.v409 N.v409 R.v410 N.v410 R.v411 N.v411 R.v412 N.v412 R.v413 N.v413 R.v414 N.v414 R.v415 N.v415 R.v416 N.v416 R.v417 N.v417 R.v418 N.v418 R.v419 N.v419 R.v420 N.v420 R.v421 N.v421 R.v422 N.v422 R.v423 N.v423 R.v424 N.v424 R.v425 N.v425 R.v426 N.v426 R.v427 N.v427 R.v428 N.v428 R.v429 N.v429 R.v430 N.v430 R.v431 N.v431 R.v432 N.v432 R.v433 N.v433 R.v434 N.v434 R.v435 N.v435 R.v436 N.v436 R.v437 N.v437 R.v438 N.v438 R.v439 N.v439 R.v440 N.v440 R.v441 N.v441 R.v442 N.v442 R.v443 N.v443 R.v444 N.v444 R.v445 N.v445.
Theorem checks_refine s i : R.assertionChecks (state s) (inputs i) = N.assertionChecks s i.
Proof. unfold R.assertionChecks, N.assertionChecks.
  rewrite ?node_6.
  rewrite ?node_8.
  rewrite ?node_399.
  rewrite ?node_414.
  rewrite ?node_416.
  rewrite ?node_418.
  rewrite ?node_419.
  rewrite ?node_421.
  rewrite ?node_430.
  rewrite ?node_431.
  rewrite ?node_433.
  rewrite ?node_435.
  rewrite ?node_438.
  rewrite ?node_440.
  rewrite ?node_443.
  rewrite ?node_444.
  rewrite ?node_445.
  reflexivity.
Qed.
Theorem asserts_refine s i : N.asserts s i <-> R.asserts (state s) (inputs i).
Proof. unfold N.asserts, R.asserts; rewrite checks_refine; reflexivity. Qed.
Print Assumptions step_refines.
Print Assumptions observe_refines.
Print Assumptions run_refines.
Print Assumptions asserts_refine.
End Radix2DividerRefinement.
