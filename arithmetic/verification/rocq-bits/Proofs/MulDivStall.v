(* Generated native-model contracts; each transfer is checked by Rocq. *)
From Stdlib Require Import ZArith Lia Zmod.Bits.
From BitsProofs Require Import MulDivRefinement.
From ReferenceProofs Require Import MulDivStall MulDivTiming.
Module NativeMulDivStall.
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
Local Opaque N.step N.run N.observe B.R.step B.R.run B.R.observe.
Theorem stall_stable s i later
  (done : word 3 (r0_nstate s)=6 \/ word 3 (r0_nstate s)=7)
  (hr : word 1 (nreset i)=0) (hk : word 1 (nio_5Fkill i)=0)
  (stall : word 1 (nio_5Fresp_5Fready i)=0) :
  nio_5Fresp_5Fvalid (observe (step s i) later)=1 /\
  nio_5Fresp_5Fbits_5Fdata (observe (step s i) later)=nio_5Fresp_5Fbits_5Fdata (observe s i) /\
  nio_5Fresp_5Fbits_5Ftag (observe (step s i) later)=nio_5Fresp_5Fbits_5Ftag (observe s i).
Proof.
  pose proof (ReferenceProofs.MulDivStall.MulDivStall.stall_stable (B.state s) (B.inputs i) (B.inputs later) done hr hk stall) as H.
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
Print Assumptions stall_stable.
Theorem stall_run_stable n s inputs
  (done : word 3 (r0_nstate s)=6 \/ word 3 (r0_nstate s)=7)
  (hold : forall t, (t<n)%nat -> word 1 (nreset (inputs t))=0 /\
    word 1 (nio_5Fkill (inputs t))=0 /\ word 1 (nio_5Fresp_5Fready (inputs t))=0) :
  word 3 (r0_nstate (run s inputs n))=word 3 (r0_nstate s) /\
  nio_5Fresp_5Fvalid (observe (run s inputs n) (inputs n))=1 /\
  nio_5Fresp_5Fbits_5Fdata (observe (run s inputs n) (inputs n))=nio_5Fresp_5Fbits_5Fdata (observe s (inputs O)) /\
  nio_5Fresp_5Fbits_5Ftag (observe (run s inputs n) (inputs n))=nio_5Fresp_5Fbits_5Ftag (observe s (inputs O)).
Proof.
  pose proof (ReferenceProofs.MulDivStall.MulDivStall.stall_run_stable n (B.state s) (fun t => B.inputs (inputs t)) done hold) as H.
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
Print Assumptions stall_run_stable.
End NativeMulDivStall.
