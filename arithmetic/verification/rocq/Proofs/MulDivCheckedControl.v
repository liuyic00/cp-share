From Coq Require Import ZArith Lia.
From Proofs Require Import MulDivActive MulDivCheckedProjection MulDivCheckedHistory.
From Generated Require Import MulDiv MulDivChecked.
Import MulDivChecked.CIRCTBits MulDivChecked.nMulDivChecked MulDivCheckedHistory.MulDivCheckedHistory.
Open Scope Z_scope.
Module MulDivCheckedControl.
Module P := MulDivCheckedProjection.MulDivCheckedProjection.
Definition Active s := MulDivActive.MulDivActive.Active (P.state s).
Definition Invariant s := word 1 (r9_ncontractPending s)=1 -> Active s.
Lemma pending_origin s i (pending : word 1 (r9_ncontractPending (step s i))=1) :
  word 1 (nreset i)=0 /\
  (v2 s i=1 \/ (v2 s i=0 /\ word 1 (r9_ncontractPending s)=1 /\ v40 s i=0)).
Proof.
  cbn [step r9_ncontractPending] in pending.
  assert (reset : word 1 (nreset i)=0).
  { destruct (bit_cases (nreset i)) as [hr|hr]; [exact hr|rewrite hr in pending; discriminate]. }
  split; [exact reset|]; rewrite reset in pending; cbn [Z.eqb] in pending.
  assert (accept : v2 s i=0 \/ v2 s i=1) by (unfold v2; apply bit_cases).
  destruct accept as [no|yes]; [right|left; exact yes].
  split; [exact no|].
  unfold v163,v162,v161,v31 in pending; rewrite no in pending; cbn [Z.eqb] in pending.
  assert (cancel : v40 s i=0 \/ v40 s i=1) by (unfold v40; apply bit_cases).
  destruct cancel as [stop|stop]; destruct (bit_cases (r9_ncontractPending s)) as [flag|flag];
    rewrite stop,flag in pending; try discriminate; split; assumption.
Qed.
Local Opaque step run MulDiv.nMulDiv.step.
Theorem reset_invariant s i (reset : word 1 (nreset i)=1) : Invariant (step s i).
Proof.
  intros flag; destruct (reset_monitors s i reset) as [pending rest].
  rewrite pending in flag; discriminate.
Qed.
Theorem step_invariant s i (previous : Invariant s) : Invariant (step s i).
Proof.
  intro pending; destruct (pending_origin s i pending) as [reset [accepted|[absent [old live]]]].
  - unfold Active; rewrite P.step_projects; apply MulDivActive.MulDivActive.capture_active.
    + rewrite <- P.node_v2; exact accepted.
    + exact reset.
  - unfold Active; rewrite P.step_projects; apply MulDivActive.MulDivActive.active_edge.
    + exact (previous old).
    + exact reset.
    + rewrite <- P.node_v40; exact live.
Qed.
Theorem run_invariant initial resetInput (reset : word 1 (nreset resetInput)=1) pins n :
  Invariant (run (step initial resetInput) pins n).
Proof.
  induction n as [|n IH].
  - exact (reset_invariant initial resetInput reset).
  - change (run (step initial resetInput) pins (S n)) with (step (run (step initial resetInput) pins n) (pins n)).
    apply step_invariant; exact IH.
Qed.
Lemma active_not_idle s (active : Active s) : word 3 (r0_nstate s)<>0.
Proof. exact (MulDivActive.MulDivActive.active_not_idle (P.state s) active). Qed.
Theorem pending_history_stable s i (control : Invariant s) (pending : word 1 (r9_ncontractPending s)=1) :
  captured (step s i)=captured s.
Proof. apply hold; left; apply active_not_idle; apply control; exact pending. Qed.
End MulDivCheckedControl.
Print Assumptions MulDivCheckedControl.run_invariant.
Print Assumptions MulDivCheckedControl.pending_history_stable.
