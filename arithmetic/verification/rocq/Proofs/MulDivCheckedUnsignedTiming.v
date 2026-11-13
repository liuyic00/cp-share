From Coq Require Import ZArith Lia List Bool.
From Proofs Require Import MulDivCheckedAge MulDivCheckedTimingChecks MulDivCheckedControl MulDivActive MulDivStall MulDivMetadata MulDivUnsignedCapture.
From Generated Require Import MulDivChecked.
Import MulDivChecked.CIRCTBits MulDivChecked.nMulDivChecked
  MulDivCheckedAge.MulDivCheckedAge MulDivCheckedTimingChecks.MulDivCheckedTimingChecks
  MulDivCheckedHistory.MulDivCheckedHistory.
Open Scope Z_scope.
Module MulDivCheckedUnsignedTiming.
Definition Operation s := word 4 (r11_ncontractFn s)=5 \/ word 4 (r11_ncontractFn s)=7.
Definition Phase s :=
  (word 3 (r0_nstate s)=3 /\ word 7 (r3_ncount s)=word 7 (r10_ncontractAge s) /\
   word 7 (r10_ncontractAge s)<=64 /\ word 1 (r4_nneg_5Fout s)=0) \/
  (word 3 (r0_nstate s)=7 /\ word 7 (r10_ncontractAge s)=65).
Definition Invariant s := word 1 (r9_ncontractPending s)=1 -> Operation s -> Phase s.
Lemma unsigned_latency s i (operation : Operation s) : v225 s i=65.
Proof.
  assert (signedZero : v194 s i=0).
  { unfold v194,v193,v31; destruct operation as [fn|fn]; rewrite fn; reflexivity. }
  assert (a : v202 s i=0) by (unfold v202; rewrite signedZero,Z.land_0_l; reflexivity).
  assert (b : v210 s i=0) by (unfold v210; rewrite signedZero,Z.land_0_l; reflexivity).
  assert (neg : v219 s i=0).
  { unfold v219,v218,v214; rewrite a,b; change (word 1 (if v213 s i=?1 then 0 else word 1 (Z.land 0 (v217 s i)))=0).
    rewrite Z.land_0_l; destruct (v213 s i=?1); reflexivity. }
  unfold v225,v222,v221,v220,v212,v211,v192,v191; rewrite a,b,neg;
    destruct operation as [fn|fn]; rewrite fn; reflexivity.
Qed.
Lemma divide_valid s i (state : word 3 (r0_nstate s)=3) : v38 s i=0.
Proof. unfold v38,v37,v36,v35,v4; rewrite state; reflexivity. Qed.
Lemma done_valid s i (state : word 3 (r0_nstate s)=7) : v38 s i=1.
Proof. unfold v38,v37,v36,v35,v4; rewrite state; reflexivity. Qed.
Theorem timing_assertions s i (invariant : Invariant s) (operation : Operation s) :
  forallb (fun b=>b) (firstn 2 (assertionChecks s i))=true.
Proof.
  apply sufficient; intro gate;
    destruct (invariant (gate_pending s i gate) operation) as [[state [count [age neg]]]|[state age]];
    rewrite unsigned_latency by exact operation.
  - lia.
  - lia.
  - rewrite (divide_valid s i state).
    assert (different : (word 7 (r10_ncontractAge s)=?65)=false) by (apply Z.eqb_neq; lia).
    rewrite different; reflexivity.
  - rewrite (done_valid s i state),age; reflexivity.
Qed.
Lemma compute_phase s i (state : word 3 (r0_nstate s)=3)
  (count : word 7 (r3_ncount s)=word 7 (r10_ncontractAge s))
  (age : word 7 (r10_ncontractAge s)<=64) (negative : word 1 (r4_nneg_5Fout s)=0)
  (pending : word 1 (r9_ncontractPending s)=1)
  (reset : word 1 (nreset i)=0) (kill : word 1 (nio_5Fkill i)=0) : Phase (step s i).
Proof.
  assert (absent : v2 s i=0) by (apply busy; lia).
  assert (increment : word 7 (r10_ncontractAge (step s i))=word 7 (r10_ncontractAge s)+1).
  { rewrite (advance s i reset absent pending (divide_valid s i state)); apply Words.word_small.
    pose proof (bounds 7 (r10_ncontractAge s) ltac:(lia)); change (2^7) with 128 in *; lia. }
  assert (next : r0_nstate (step s i)=if word 7 (r3_ncount s)=?64 then 7 else 3).
  { change (r0_nstate (step s i)) with (MulDiv.nMulDiv.r0_nstate (P.state (step s i))).
    rewrite P.step_projects, (MulDivControl.MulDivControl.div_state (P.state s) (P.inputs i) state reset kill).
    change (MulDiv.CIRCTBits.word 1 (MulDiv.nMulDiv.r4_nneg_5Fout (P.state s))) with (word 1 (r4_nneg_5Fout s)).
    rewrite negative; reflexivity. }
  assert (counter : word 7 (r3_ncount (step s i))=word 7 (r10_ncontractAge s)+1).
  { change (word 7 (MulDiv.nMulDiv.r3_ncount (P.state (step s i)))=word 7 (r10_ncontractAge s)+1).
    rewrite P.step_projects, (MulDivControl.MulDivControl.compute_count (P.state s) (P.inputs i) (or_intror state)).
    change (word 7 (word 7 (word 7 (r3_ncount s)+1))=word 7 (r10_ncontractAge s)+1).
    rewrite normalize,count by lia; apply Words.word_small.
    pose proof (bounds 7 (r10_ncontractAge s) ltac:(lia)); change (2^7) with 128 in *; lia. }
  assert (neg : r4_nneg_5Fout (step s i)=0).
  { change (MulDiv.nMulDiv.r4_nneg_5Fout (P.state (step s i))=0).
    rewrite P.step_projects; apply MulDivMetadata.MulDivMetadata.nonnegative_edge; assumption. }
  unfold Phase; destruct (word 7 (r3_ncount s)=?64) eqn:last.
  - apply Z.eqb_eq in last; right; rewrite next,increment; split; [reflexivity|lia].
  - apply Z.eqb_neq in last; left; rewrite next,counter,increment,neg; repeat split; try reflexivity; lia.
Qed.
Lemma capture_phase s i (accepted : v2 s i=1) (reset : word 1 (nreset i)=0)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn i)=5 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=7) : Phase (step s i).
Proof.
  destruct (MulDivUnsignedCapture.MulDivUnsignedCapture.decode (P.state s) (P.inputs i) operation)
    as [mul [a [b high]]].
  rewrite <-P.node_v6 in mul; rewrite <-P.node_v20 in a; rewrite <-P.node_v29 in b;
    rewrite <-P.node_v79 in high.
  unfold Phase; left; cbn [step r0_nstate r3_ncount r10_ncontractAge r4_nneg_5Fout].
  rewrite reset; unfold v61,v34,v33,v32,v30,v73,v67,v66,v65,v168,v92,v81,v80,v82,v8,v31.
  change (MulDiv.CIRCTBits.word 4 (MulDiv.nMulDiv.nio_5Freq_5Fbits_5Ffn (P.inputs i))) with (word 4 (nio_5Freq_5Fbits_5Ffn i)) in high.
  rewrite accepted,mul,a,b,high.
  destruct (word 4 (nio_5Freq_5Fbits_5Ffn i)=?7); vm_compute; intuition discriminate.
Qed.
Lemma hold_phase s i (state : word 3 (r0_nstate s)=7)
  (age : word 7 (r10_ncontractAge s)=65)
  (reset : word 1 (nreset i)=0) (live : v40 s i=0) : Phase (step s i).
Proof.
  assert (absent : v2 s i=0) by (apply busy; lia).
  assert (corelive : MulDiv.nMulDiv.v40 (P.state s) (P.inputs i)=0) by (rewrite <-P.node_v40; exact live).
  pose proof (MulDivActive.MulDivActive.uncancelled _ _ corelive) as kill.
  assert (done : MulDiv.CIRCTBits.word 3 (MulDiv.nMulDiv.r0_nstate (P.state s))=6 \/
    MulDiv.CIRCTBits.word 3 (MulDiv.nMulDiv.r0_nstate (P.state s))=7) by (right; exact state).
  pose proof (MulDivActive.MulDivActive.stalled_done _ _ done corelive) as ready.
  destruct (MulDivStall.MulDivStall.done_registers (P.state s) (P.inputs i) done reset kill ready) as [next rest].
  unfold Phase; right; split.
  - change (word 3 (MulDiv.nMulDiv.r0_nstate (P.state (step s i)))=7).
    rewrite P.step_projects,next; change (word 3 (word 3 (r0_nstate s))=7).
    rewrite normalize by lia; exact state.
  - rewrite (hold_done s i reset absent (done_valid s i state)); exact age.
Qed.
Theorem reset_invariant s i (reset : word 1 (nreset i)=1) : Invariant (step s i).
Proof.
  intros pending operation; destruct (reset_monitors s i reset) as [flag rest].
  rewrite flag in pending; discriminate.
Qed.
Theorem step_invariant s i (previous : Invariant s) : Invariant (step s i).
Proof.
  intros pending operation.
  destruct (MulDivCheckedControl.MulDivCheckedControl.pending_origin s i pending)
    as [reset [accepted|[absent [old live]]]].
  - apply capture_phase; try assumption.
    unfold Operation in operation; cbn [step r11_ncontractFn] in operation.
    unfold v169 in operation; rewrite accepted in operation; cbn [Z.eqb Pos.eqb] in operation;
      repeat rewrite normalize in operation by lia; exact operation.
  - assert (oldOperation : Operation s) by (unfold Operation in *; rewrite (fn_hold s i absent) in operation; exact operation).
    destruct (previous old oldOperation) as [[state [count [age negative]]]|[state age]].
    + apply compute_phase; try assumption.
      apply (MulDivActive.MulDivActive.uncancelled (P.state s) (P.inputs i)).
      rewrite <-P.node_v40; exact live.
    + apply hold_phase; assumption.
Qed.
Local Opaque run step.
Theorem run_invariant initial resetInput (reset : word 1 (nreset resetInput)=1) pins n :
  Invariant (run (step initial resetInput) pins n).
Proof.
  induction n as [|n IH]; [apply reset_invariant; exact reset|].
  change (run (step initial resetInput) pins (S n)) with
    (step (run (step initial resetInput) pins n) (pins n)); apply step_invariant; exact IH.
Qed.
Theorem timing_assertions_after_reset initial resetInput (reset : word 1 (nreset resetInput)=1) pins n
  (operation : Operation (run (step initial resetInput) pins n)) :
  forallb (fun b=>b) (firstn 2 (assertionChecks (run (step initial resetInput) pins n) (pins n)))=true.
Proof. apply timing_assertions; [apply run_invariant; exact reset|exact operation]. Qed.
End MulDivCheckedUnsignedTiming.
Print Assumptions MulDivCheckedUnsignedTiming.timing_assertions_after_reset.
Print Assumptions MulDivCheckedUnsignedTiming.compute_phase.
