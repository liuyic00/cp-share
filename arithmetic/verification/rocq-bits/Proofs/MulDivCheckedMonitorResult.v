(* Generated native-model contracts; each transfer is checked by Rocq. *)
From Stdlib Require Import ZArith Lia Zmod.Bits.
From BitsProofs Require Import MulDivCheckedRefinement.
From ReferenceProofs Require Import MulDivCheckedMonitorResult MulDivTiming.
Module NativeMulDivCheckedMonitorResult.
Module B := BitsProofs.MulDivCheckedRefinement.MulDivCheckedRefinement.
Module N := B.N.
Open Scope Z_scope.
Definition word := B.RB.word.
Definition step := N.step.
Definition run := N.run.
Definition observe := N.observe.
Definition asserts := N.asserts.
Definition nreset (x : N.Inputs) : Z := Zmod.unsigned (N.nreset x).
Definition nio_5Freq_5Fvalid (x : N.Inputs) : Z := Zmod.unsigned (N.nio_5Freq_5Fvalid x).
Definition nio_5Freq_5Fbits_5Ffn (x : N.Inputs) : Z := Zmod.unsigned (N.nio_5Freq_5Fbits_5Ffn x).
Definition nio_5Freq_5Fbits_5Fdw (x : N.Inputs) : Z := Zmod.unsigned (N.nio_5Freq_5Fbits_5Fdw x).
Definition nio_5Freq_5Fbits_5Fin1 (x : N.Inputs) : Z := Zmod.unsigned (N.nio_5Freq_5Fbits_5Fin1 x).
Definition nio_5Freq_5Fbits_5Fin2 (x : N.Inputs) : Z := Zmod.unsigned (N.nio_5Freq_5Fbits_5Fin2 x).
Definition nio_5Freq_5Fbits_5Ftag (x : N.Inputs) : Z := Zmod.unsigned (N.nio_5Freq_5Fbits_5Ftag x).
Definition nio_5Fkill (x : N.Inputs) : Z := Zmod.unsigned (N.nio_5Fkill x).
Definition nio_5Fresp_5Fready (x : N.Inputs) : Z := Zmod.unsigned (N.nio_5Fresp_5Fready x).
Definition r0_nstate (x : N.State) : Z := Zmod.unsigned (N.r0_nstate x).
Definition r1_nreq_5Fdw (x : N.State) : Z := Zmod.unsigned (N.r1_nreq_5Fdw x).
Definition r2_nreq_5Ftag (x : N.State) : Z := Zmod.unsigned (N.r2_nreq_5Ftag x).
Definition r3_ncount (x : N.State) : Z := Zmod.unsigned (N.r3_ncount x).
Definition r4_nneg_5Fout (x : N.State) : Z := Zmod.unsigned (N.r4_nneg_5Fout x).
Definition r5_nisHi (x : N.State) : Z := Zmod.unsigned (N.r5_nisHi x).
Definition r6_nresHi (x : N.State) : Z := Zmod.unsigned (N.r6_nresHi x).
Definition r7_ndivisor (x : N.State) : Z := Zmod.unsigned (N.r7_ndivisor x).
Definition r8_nremainder (x : N.State) : Z := Zmod.unsigned (N.r8_nremainder x).
Definition r9_ncontractPending (x : N.State) : Z := Zmod.unsigned (N.r9_ncontractPending x).
Definition r10_ncontractAge (x : N.State) : Z := Zmod.unsigned (N.r10_ncontractAge x).
Definition r11_ncontractFn (x : N.State) : Z := Zmod.unsigned (N.r11_ncontractFn x).
Definition r12_ncontractDw (x : N.State) : Z := Zmod.unsigned (N.r12_ncontractDw x).
Definition r13_ncontractA (x : N.State) : Z := Zmod.unsigned (N.r13_ncontractA x).
Definition r14_ncontractB (x : N.State) : Z := Zmod.unsigned (N.r14_ncontractB x).
Definition r15_ncontractTag (x : N.State) : Z := Zmod.unsigned (N.r15_ncontractTag x).
Definition r16_ncontractWasNegated (x : N.State) : Z := Zmod.unsigned (N.r16_ncontractWasNegated x).
Definition r17_ncontractQuotient (x : N.State) : Z := Zmod.unsigned (N.r17_ncontractQuotient x).
Definition r18_ncontractResidue (x : N.State) : Z := Zmod.unsigned (N.r18_ncontractResidue x).
Definition r19_ncontractPreviousData (x : N.State) : Z := Zmod.unsigned (N.r19_ncontractPreviousData x).
Definition r20_ncontractPreviousTag (x : N.State) : Z := Zmod.unsigned (N.r20_ncontractPreviousTag x).
Definition r21_ncontractWasStalled (x : N.State) : Z := Zmod.unsigned (N.r21_ncontractWasStalled x).
Definition nio_5Freq_5Fready (x : N.Outputs) : Z := Zmod.unsigned (N.nio_5Freq_5Fready x).
Definition nio_5Fresp_5Fvalid (x : N.Outputs) : Z := Zmod.unsigned (N.nio_5Fresp_5Fvalid x).
Definition nio_5Fresp_5Fbits_5Fdata (x : N.Outputs) : Z := Zmod.unsigned (N.nio_5Fresp_5Fbits_5Fdata x).
Definition nio_5Fresp_5Fbits_5Ftag (x : N.Outputs) : Z := Zmod.unsigned (N.nio_5Fresp_5Fbits_5Ftag x).
Module S := ReferenceProofs.MulDivCheckedMonitorResult.MulDivCheckedMonitorResult.S.
Module P.
Definition inputs (i : N.Inputs) := ReferenceProofs.MulDivCheckedMonitorResult.MulDivCheckedMonitorResult.P.inputs (B.inputs i).
End P.
Module L.
Definition latency (s : N.State) := ReferenceProofs.MulDivCheckedMonitorResult.MulDivCheckedMonitorResult.L.latency (B.state s).
End L.
Local Opaque N.step N.run N.observe B.R.step B.R.run B.R.observe.
Theorem signed_result_at_monitor_cycle s pins
  (idle : word 3 (r0_nstate s)=0)
  (valid : word 1 (nio_5Freq_5Fvalid (pins O))=1)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn (pins O))=4 \/ word 4 (nio_5Freq_5Fbits_5Ffn (pins O))=6)
  (resets : forall t, (t<68)%nat -> word 1 (nreset (pins t))=0)
  (kills : forall t, (t<68)%nat -> word 1 (nio_5Fkill (pins t))=0) :
  let n := (Z.to_nat (L.latency (step s (pins O)))+1)%nat in
  nio_5Fresp_5Fvalid (observe (run s pins n) (pins n))=1 /\
  nio_5Fresp_5Fbits_5Fdata (observe (run s pins n) (pins n))=S.specification (P.inputs (pins O)) /\
  nio_5Fresp_5Fbits_5Ftag (observe (run s pins n) (pins n))=word 5 (nio_5Freq_5Fbits_5Ftag (pins O)).
Proof.
  pose proof (ReferenceProofs.MulDivCheckedMonitorResult.MulDivCheckedMonitorResult.signed_result_at_monitor_cycle (B.state s) (fun t => B.inputs (pins t)) idle valid operation resets kills) as H.
  cbn beta zeta in H.
  repeat progress rewrite <-B.step_refines in H.
  repeat progress rewrite <-B.run_refines in H.
  repeat progress rewrite B.output_nio_5Freq_5Fready in H.
  repeat progress rewrite B.output_nio_5Fresp_5Fvalid in H.
  repeat progress rewrite B.output_nio_5Fresp_5Fbits_5Fdata in H.
  repeat progress rewrite B.output_nio_5Fresp_5Fbits_5Ftag in H.
  repeat progress rewrite B.state_r0_nstate in H.
  repeat progress rewrite B.state_r1_nreq_5Fdw in H.
  repeat progress rewrite B.state_r2_nreq_5Ftag in H.
  repeat progress rewrite B.state_r3_ncount in H.
  repeat progress rewrite B.state_r4_nneg_5Fout in H.
  repeat progress rewrite B.state_r5_nisHi in H.
  repeat progress rewrite B.state_r6_nresHi in H.
  repeat progress rewrite B.state_r7_ndivisor in H.
  repeat progress rewrite B.state_r8_nremainder in H.
  repeat progress rewrite B.state_r9_ncontractPending in H.
  repeat progress rewrite B.state_r10_ncontractAge in H.
  repeat progress rewrite B.state_r11_ncontractFn in H.
  repeat progress rewrite B.state_r12_ncontractDw in H.
  repeat progress rewrite B.state_r13_ncontractA in H.
  repeat progress rewrite B.state_r14_ncontractB in H.
  repeat progress rewrite B.state_r15_ncontractTag in H.
  repeat progress rewrite B.state_r16_ncontractWasNegated in H.
  repeat progress rewrite B.state_r17_ncontractQuotient in H.
  repeat progress rewrite B.state_r18_ncontractResidue in H.
  repeat progress rewrite B.state_r19_ncontractPreviousData in H.
  repeat progress rewrite B.state_r20_ncontractPreviousTag in H.
  repeat progress rewrite B.state_r21_ncontractWasStalled in H.
  repeat progress rewrite B.inputs_nreset in H.
  repeat progress rewrite B.inputs_nio_5Freq_5Fvalid in H.
  repeat progress rewrite B.inputs_nio_5Freq_5Fbits_5Ffn in H.
  repeat progress rewrite B.inputs_nio_5Freq_5Fbits_5Fdw in H.
  repeat progress rewrite B.inputs_nio_5Freq_5Fbits_5Fin1 in H.
  repeat progress rewrite B.inputs_nio_5Freq_5Fbits_5Fin2 in H.
  repeat progress rewrite B.inputs_nio_5Freq_5Fbits_5Ftag in H.
  repeat progress rewrite B.inputs_nio_5Fkill in H.
  repeat progress rewrite B.inputs_nio_5Fresp_5Fready in H.
  exact H.
Qed.
Print Assumptions signed_result_at_monitor_cycle.
End NativeMulDivCheckedMonitorResult.
