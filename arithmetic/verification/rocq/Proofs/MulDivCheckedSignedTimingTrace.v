From Coq Require Import ZArith Lia List Bool.
From Proofs Require Import MulDivCheckedSignedTimingCapture.
From Generated Require Import MulDivChecked.
Import MulDivChecked.CIRCTBits MulDivChecked.nMulDivChecked
  MulDivCheckedHistory.MulDivCheckedHistory MulDivCheckedAge.MulDivCheckedAge
  MulDivCheckedSignedTiming.MulDivCheckedSignedTiming
  MulDivCheckedSignedTimingEdges.MulDivCheckedSignedTimingEdges
  MulDivCheckedSignedTimingInit.MulDivCheckedSignedTimingInit
  MulDivCheckedSignedTimingCapture.MulDivCheckedSignedTimingCapture.
Open Scope Z_scope.
Module MulDivCheckedSignedTimingTrace.
Definition Phases s := Negating s \/ Prepared s \/ LatePhases s.
Definition Invariant s := word 1 (r9_ncontractPending s)=1 -> Operation s -> Phases s.
Lemma accepted_idle s i (accepted : v2 s i=1) : word 3 (r0_nstate s)=0 /\ word 1 (nio_5Freq_5Fvalid i)=1.
Proof.
  unfold v2,v1,v0 in accepted; change (word 3 0) with 0 in accepted.
  destruct (word 3 (r0_nstate s)=?0) eqn:idle; [apply Z.eqb_eq in idle|discriminate].
  destruct (bit_cases (nio_5Freq_5Fvalid i)) as [valid|valid]; rewrite valid in accepted; try discriminate; split; assumption.
Qed.
Theorem reset_invariant s i (reset : word 1 (nreset i)=1) : Invariant (step s i).
Proof. intros pending operation; destruct (reset_monitors s i reset) as [flag rest]; rewrite flag in pending; discriminate. Qed.
Theorem step_invariant s i (previous : Invariant s) : Invariant (step s i).
Proof.
  intros pending operation.
  destruct (MulDivCheckedControl.MulDivCheckedControl.pending_origin s i pending)
    as [reset [accepted|[absent [old live]]]].
  - destruct (accepted_idle s i accepted) as [idle valid].
    assert (op : word 4 (nio_5Freq_5Fbits_5Ffn i)=4 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=6).
    { unfold Operation in operation; cbn [step r11_ncontractFn] in operation.
      unfold v169 in operation; rewrite accepted in operation; cbn [Z.eqb Pos.eqb] in operation;
        repeat rewrite normalize in operation by lia; exact operation. }
    destruct (capture_phase s i idle valid reset op) as [neg|prepared]; [left|right; left]; assumption.
  - assert (op : Operation s) by (unfold Operation in *; rewrite (fn_hold s i absent) in operation; exact operation).
    assert (kill : word 1 (nio_5Fkill i)=0).
    { apply (MulDivActive.MulDivActive.uncancelled (P.state s) (P.inputs i)); rewrite <-P.node_v40; exact live. }
    destruct (previous old op) as [neg|[prepared|late]].
    + right; left; apply input_negation_edge; assumption.
    + right; right; apply first_edge; assumption.
    + right; right; apply late_edge; assumption.
Qed.
Local Opaque run step.
Theorem run_invariant initial resetInput (reset : word 1 (nreset resetInput)=1) pins n :
  Invariant (run (step initial resetInput) pins n).
Proof.
  induction n as [|n IH]; [apply reset_invariant; exact reset|].
  change (run (step initial resetInput) pins (S n)) with
    (step (run (step initial resetInput) pins n) (pins n)); apply step_invariant; exact IH.
Qed.
Lemma timing_phases s (phases : Phases s) : TimingPhases s.
Proof.
  destruct phases as [neg|[prepared|late]].
  - left; unfold Negating in neg; intuition.
  - apply prepared_timing; exact prepared.
  - apply timing_projection; exact late.
Qed.
Theorem timing_assertions_after_reset initial resetInput (reset : word 1 (nreset resetInput)=1) pins n
  (operation : Operation (run (step initial resetInput) pins n)) :
  forallb (fun b=>b) (firstn 2 (assertionChecks (run (step initial resetInput) pins n) (pins n)))=true.
Proof.
  apply timing_assertions; [exact operation|intro pending; apply timing_phases].
  exact (run_invariant initial resetInput reset pins n pending operation).
Qed.
End MulDivCheckedSignedTimingTrace.
Print Assumptions MulDivCheckedSignedTimingTrace.timing_assertions_after_reset.
