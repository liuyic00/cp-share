(* Generated native-model contracts; each transfer is checked by Rocq. *)
From Stdlib Require Import ZArith Lia Zmod.Bits.
From BitsProofs Require Import MulDivRefinement.
From ReferenceProofs Require Import MulDivSigned MulDivTiming.
Module NativeMulDivSigned.
Module B := BitsProofs.MulDivRefinement.MulDivRefinement.
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
Definition nio_5Freq_5Fready (x : N.Outputs) : Z := Zmod.unsigned (N.nio_5Freq_5Fready x).
Definition nio_5Fresp_5Fvalid (x : N.Outputs) : Z := Zmod.unsigned (N.nio_5Fresp_5Fvalid x).
Definition nio_5Fresp_5Fbits_5Fdata (x : N.Outputs) : Z := Zmod.unsigned (N.nio_5Fresp_5Fbits_5Fdata x).
Definition nio_5Fresp_5Fbits_5Ftag (x : N.Outputs) : Z := Zmod.unsigned (N.nio_5Fresp_5Fbits_5Ftag x).
Definition specification (i : N.Inputs) := ReferenceProofs.MulDivSigned.MulDivSigned.specification (B.inputs i).
Definition acceptedEdges (i : N.Inputs) := ReferenceProofs.MulDivSigned.MulDivSigned.acceptedEdges (B.inputs i).
Definition active (pins : nat -> N.Inputs) n := ReferenceProofs.MulDivTiming.MulDivTiming.active (fun t => B.inputs (pins t)) n.
Local Opaque N.step N.run N.observe B.R.step B.R.run B.R.observe.
Theorem accepted_result_exact s inputs (idle : word 3 (r0_nstate s)=0)
  (valid : word 1 (nio_5Freq_5Fvalid (inputs O))=1)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=4 \/ word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=6)
  (live : active inputs 68) :
  exists n, n=acceptedEdges (inputs O) /\ (66<=n<=68)%nat /\
  nio_5Fresp_5Fvalid (observe (run s inputs n) (inputs n))=1 /\
  nio_5Fresp_5Fbits_5Fdata (observe (run s inputs n) (inputs n))=specification (inputs O) /\
  nio_5Fresp_5Fbits_5Ftag (observe (run s inputs n) (inputs n))=word 5 (nio_5Freq_5Fbits_5Ftag (inputs O)).
Proof.
  pose proof (ReferenceProofs.MulDivSigned.MulDivSigned.accepted_result_exact (B.state s) (fun t => B.inputs (inputs t)) idle valid operation live) as H.
  destruct H as [n H]; exists n.
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
Print Assumptions accepted_result_exact.
Theorem after_reset_result initial resetInput inputs (hr : word 1 (nreset resetInput)=1)
  (valid : word 1 (nio_5Freq_5Fvalid (inputs O))=1)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=4 \/ word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=6)
  (live : active inputs 68) :
  exists n, n=acceptedEdges (inputs O) /\ (66<=n<=68)%nat /\
  nio_5Fresp_5Fvalid (observe (run (step initial resetInput) inputs n) (inputs n))=1 /\
  nio_5Fresp_5Fbits_5Fdata (observe (run (step initial resetInput) inputs n) (inputs n))=specification (inputs O) /\
  nio_5Fresp_5Fbits_5Ftag (observe (run (step initial resetInput) inputs n) (inputs n))=word 5 (nio_5Freq_5Fbits_5Ftag (inputs O)).
Proof.
  pose proof (ReferenceProofs.MulDivSigned.MulDivSigned.after_reset_result (B.state initial) (B.inputs resetInput) (fun t => B.inputs (inputs t)) hr valid operation live) as H.
  destruct H as [n H]; exists n.
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
Print Assumptions after_reset_result.
End NativeMulDivSigned.
