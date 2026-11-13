(* Generated native-model contracts; each transfer is checked by Rocq. *)
From Stdlib Require Import ZArith Lia Zmod.Bits.
From BitsProofs Require Import Radix2DividerRefinement.
From ReferenceProofs Require Import RadixOutput MulDivTiming.
Module NativeRadixOutput.
Module B := BitsProofs.Radix2DividerRefinement.Radix2DividerRefinement.
Module N := B.N.
Open Scope Z_scope.
Definition word := B.RB.word.
Definition step := N.step.
Definition run := N.run.
Definition observe := N.observe.
Definition asserts := N.asserts.
Definition nreset (x : N.Inputs) : Z := Zmod.unsigned (N.nreset x).
Definition nio_5Fin_5Fvalid (x : N.Inputs) : Z := Zmod.unsigned (N.nio_5Fin_5Fvalid x).
Definition nio_5Fin_5Fbits_5Fsrc_5F0 (x : N.Inputs) : Z := Zmod.unsigned (N.nio_5Fin_5Fbits_5Fsrc_5F0 x).
Definition nio_5Fin_5Fbits_5Fsrc_5F1 (x : N.Inputs) : Z := Zmod.unsigned (N.nio_5Fin_5Fbits_5Fsrc_5F1 x).
Definition nio_5Fin_5Fbits_5Fsrc_5F2 (x : N.Inputs) : Z := Zmod.unsigned (N.nio_5Fin_5Fbits_5Fsrc_5F2 x).
Definition nio_5Fout_5Fready (x : N.Inputs) : Z := Zmod.unsigned (N.nio_5Fout_5Fready x).
Definition nctrl_5Fsign (x : N.Inputs) : Z := Zmod.unsigned (N.nctrl_5Fsign x).
Definition nctrl_5FisW (x : N.Inputs) : Z := Zmod.unsigned (N.nctrl_5FisW x).
Definition nctrl_5FisHi (x : N.Inputs) : Z := Zmod.unsigned (N.nctrl_5FisHi x).
Definition r0_nstate (x : N.State) : Z := Zmod.unsigned (N.r0_nstate x).
Definition r1_ndivBy0Reg (x : N.State) : Z := Zmod.unsigned (N.r1_ndivBy0Reg x).
Definition r2_nshiftReg (x : N.State) : Z := Zmod.unsigned (N.r2_nshiftReg x).
Definition r3_naSignReg (x : N.State) : Z := Zmod.unsigned (N.r3_naSignReg x).
Definition r4_nqSignReg (x : N.State) : Z := Zmod.unsigned (N.r4_nqSignReg x).
Definition r5_nbReg (x : N.State) : Z := Zmod.unsigned (N.r5_nbReg x).
Definition r6_naValx2Reg (x : N.State) : Z := Zmod.unsigned (N.r6_naValx2Reg x).
Definition r7_nctrlReg_5FisW (x : N.State) : Z := Zmod.unsigned (N.r7_nctrlReg_5FisW x).
Definition r8_nctrlReg_5FisHi (x : N.State) : Z := Zmod.unsigned (N.r8_nctrlReg_5FisHi x).
Definition r9_ncnt_5Fvalue (x : N.State) : Z := Zmod.unsigned (N.r9_ncnt_5Fvalue x).
Definition r10_nhistoryValid (x : N.State) : Z := Zmod.unsigned (N.r10_nhistoryValid x).
Definition r11_npreviousState (x : N.State) : Z := Zmod.unsigned (N.r11_npreviousState x).
Definition r12_npreviousCount (x : N.State) : Z := Zmod.unsigned (N.r12_npreviousCount x).
Definition r13_nwasStalled (x : N.State) : Z := Zmod.unsigned (N.r13_nwasStalled x).
Definition r14_npreviousOutput (x : N.State) : Z := Zmod.unsigned (N.r14_npreviousOutput x).
Definition nio_5Fin_5Fready (x : N.Outputs) : Z := Zmod.unsigned (N.nio_5Fin_5Fready x).
Definition nio_5Fout_5Fvalid (x : N.Outputs) : Z := Zmod.unsigned (N.nio_5Fout_5Fvalid x).
Definition nio_5Fout_5Fbits_5Fdata (x : N.Outputs) : Z := Zmod.unsigned (N.nio_5Fout_5Fbits_5Fdata x).
Definition specification (i : N.Inputs) := ReferenceProofs.RadixOutput.RadixOutput.specification (B.inputs i).
Local Opaque N.step N.run N.observe B.R.step B.R.run B.R.observe.
Theorem accepted_result s inputs
  (idle : word 3 (r0_nstate s) = 0)
  (valid : word 1 (nio_5Fin_5Fvalid (inputs O)) = 1)
  (reset : forall t, (t < 67)%nat -> word 1 (nreset (inputs t)) = 0) :
  exists n, (4 <= n <= 67)%nat /\
    nio_5Fout_5Fvalid (observe (run s inputs n) (inputs n)) = 1 /\
    nio_5Fout_5Fbits_5Fdata (observe (run s inputs n) (inputs n)) = specification (inputs O).
Proof.
  pose proof (ReferenceProofs.RadixOutput.RadixOutput.accepted_result (B.state s) (fun t => B.inputs (inputs t)) idle valid reset) as H.
  destruct H as [n H]; exists n.
  cbn beta zeta in H.
  repeat progress rewrite <-B.step_refines in H.
  repeat progress rewrite <-B.run_refines in H.
  repeat progress rewrite B.output_nio_5Fin_5Fready in H.
  repeat progress rewrite B.output_nio_5Fout_5Fvalid in H.
  repeat progress rewrite B.output_nio_5Fout_5Fbits_5Fdata in H.
  repeat progress rewrite B.state_r0_nstate in H.
  repeat progress rewrite B.state_r1_ndivBy0Reg in H.
  repeat progress rewrite B.state_r2_nshiftReg in H.
  repeat progress rewrite B.state_r3_naSignReg in H.
  repeat progress rewrite B.state_r4_nqSignReg in H.
  repeat progress rewrite B.state_r5_nbReg in H.
  repeat progress rewrite B.state_r6_naValx2Reg in H.
  repeat progress rewrite B.state_r7_nctrlReg_5FisW in H.
  repeat progress rewrite B.state_r8_nctrlReg_5FisHi in H.
  repeat progress rewrite B.state_r9_ncnt_5Fvalue in H.
  repeat progress rewrite B.state_r10_nhistoryValid in H.
  repeat progress rewrite B.state_r11_npreviousState in H.
  repeat progress rewrite B.state_r12_npreviousCount in H.
  repeat progress rewrite B.state_r13_nwasStalled in H.
  repeat progress rewrite B.state_r14_npreviousOutput in H.
  repeat progress rewrite B.inputs_nreset in H.
  repeat progress rewrite B.inputs_nio_5Fin_5Fvalid in H.
  repeat progress rewrite B.inputs_nio_5Fin_5Fbits_5Fsrc_5F0 in H.
  repeat progress rewrite B.inputs_nio_5Fin_5Fbits_5Fsrc_5F1 in H.
  repeat progress rewrite B.inputs_nio_5Fin_5Fbits_5Fsrc_5F2 in H.
  repeat progress rewrite B.inputs_nio_5Fout_5Fready in H.
  repeat progress rewrite B.inputs_nctrl_5Fsign in H.
  repeat progress rewrite B.inputs_nctrl_5FisW in H.
  repeat progress rewrite B.inputs_nctrl_5FisHi in H.
  exact H.
Qed.
Print Assumptions accepted_result.
Theorem after_reset_result initial resetInput inputs
  (resetEdge : word 1 (nreset resetInput) = 1)
  (valid : word 1 (nio_5Fin_5Fvalid (inputs O)) = 1)
  (reset : forall t, (t < 67)%nat -> word 1 (nreset (inputs t)) = 0) :
  exists n, (4 <= n <= 67)%nat /\
    nio_5Fout_5Fvalid (observe (run (step initial resetInput) inputs n) (inputs n)) = 1 /\
    nio_5Fout_5Fbits_5Fdata (observe (run (step initial resetInput) inputs n) (inputs n)) = specification (inputs O).
Proof.
  pose proof (ReferenceProofs.RadixOutput.RadixOutput.after_reset_result (B.state initial) (B.inputs resetInput) (fun t => B.inputs (inputs t)) resetEdge valid reset) as H.
  destruct H as [n H]; exists n.
  cbn beta zeta in H.
  repeat progress rewrite <-B.step_refines in H.
  repeat progress rewrite <-B.run_refines in H.
  repeat progress rewrite B.output_nio_5Fin_5Fready in H.
  repeat progress rewrite B.output_nio_5Fout_5Fvalid in H.
  repeat progress rewrite B.output_nio_5Fout_5Fbits_5Fdata in H.
  repeat progress rewrite B.state_r0_nstate in H.
  repeat progress rewrite B.state_r1_ndivBy0Reg in H.
  repeat progress rewrite B.state_r2_nshiftReg in H.
  repeat progress rewrite B.state_r3_naSignReg in H.
  repeat progress rewrite B.state_r4_nqSignReg in H.
  repeat progress rewrite B.state_r5_nbReg in H.
  repeat progress rewrite B.state_r6_naValx2Reg in H.
  repeat progress rewrite B.state_r7_nctrlReg_5FisW in H.
  repeat progress rewrite B.state_r8_nctrlReg_5FisHi in H.
  repeat progress rewrite B.state_r9_ncnt_5Fvalue in H.
  repeat progress rewrite B.state_r10_nhistoryValid in H.
  repeat progress rewrite B.state_r11_npreviousState in H.
  repeat progress rewrite B.state_r12_npreviousCount in H.
  repeat progress rewrite B.state_r13_nwasStalled in H.
  repeat progress rewrite B.state_r14_npreviousOutput in H.
  repeat progress rewrite B.inputs_nreset in H.
  repeat progress rewrite B.inputs_nio_5Fin_5Fvalid in H.
  repeat progress rewrite B.inputs_nio_5Fin_5Fbits_5Fsrc_5F0 in H.
  repeat progress rewrite B.inputs_nio_5Fin_5Fbits_5Fsrc_5F1 in H.
  repeat progress rewrite B.inputs_nio_5Fin_5Fbits_5Fsrc_5F2 in H.
  repeat progress rewrite B.inputs_nio_5Fout_5Fready in H.
  repeat progress rewrite B.inputs_nctrl_5Fsign in H.
  repeat progress rewrite B.inputs_nctrl_5FisW in H.
  repeat progress rewrite B.inputs_nctrl_5FisHi in H.
  exact H.
Qed.
Print Assumptions after_reset_result.
End NativeRadixOutput.
