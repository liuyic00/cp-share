From Coq Require Import ZArith Lia.
From Proofs Require Import MulDivCheckedDivisionSign.
From Generated Require Import MulDivChecked.
Import MulDivChecked.CIRCTBits MulDivChecked.nMulDivChecked
  MulDivCheckedHistory.MulDivCheckedHistory MulDivCheckedAge.MulDivCheckedAge
  MulDivCheckedLatency.MulDivCheckedLatency MulDivCheckedDivisionOutput.MulDivCheckedDivisionOutput.
Open Scope Z_scope.
Module MulDivCheckedDivisionOutputControl.
Module D := MulDivCheckedDivisionTrace.MulDivCheckedDivisionTrace.
Definition HighInvariant s := word 1 (r9_ncontractPending s)=1 -> D.Operation s -> word 1 (r5_nisHi s)=hi s.
Lemma capture_high s i (accepted : v2 s i=1) (op : D.Operation (step s i)) : word 1 (r5_nisHi (step s i))=hi (step s i).
Proof.
  assert (fn : word 4 (r11_ncontractFn (step s i))=word 4 (nio_5Freq_5Fbits_5Ffn i)).
  { cbn [step r11_ncontractFn]; unfold v169; rewrite accepted; cbn [Z.eqb Pos.eqb]; repeat rewrite normalize by lia; reflexivity. }
  unfold D.Operation in op; rewrite fn in op.
  unfold hi; rewrite fn; cbn [step r5_nisHi]; unfold v93; rewrite accepted; cbn [Z.eqb Pos.eqb].
  unfold v79,v78,v77,v76,v75,v74,v15,v12,v6,v5,v4,v3.
  destruct op as [f|[f|[f|f]]]; rewrite f; reflexivity.
Qed.
Lemma high_step s i (previous : HighInvariant s) : HighInvariant (step s i).
Proof.
  intros pending op; destruct (MulDivCheckedControl.MulDivCheckedControl.pending_origin s i pending)
    as [reset [accepted|[absent [old live]]]].
  - apply capture_high; assumption.
  - assert (oldOp : D.Operation s) by (unfold D.Operation in *; rewrite (fn_hold s i absent) in op; exact op).
    unfold hi; rewrite (fn_hold s i absent).
    cbn [step r5_nisHi]; unfold v93; rewrite absent; cbn [Z.eqb]; repeat rewrite normalize by lia.
    exact (previous old oldOp).
Qed.
Local Opaque run step.
Theorem high_after_reset initial resetInput (reset : word 1 (nreset resetInput)=1) pins n :
  HighInvariant (run (step initial resetInput) pins n).
Proof.
  induction n as [|n IH].
  - change (HighInvariant (step initial resetInput)); intros pending op; destruct (reset_monitors initial resetInput reset) as [flag rest]; rewrite flag in pending; discriminate.
  - change (run (step initial resetInput) pins (S n)) with (step (run (step initial resetInput) pins n) (pins n)); apply high_step; exact IH.
Qed.
Theorem hold_relation s i (state : word 3 (r0_nstate s)=7)
  (reset : word 1 (nreset i)=0) (kill : word 1 (nio_5Fkill i)=0)
  (ready : word 1 (nio_5Fresp_5Fready i)=0) (relation : ResultRelation s) : ResultRelation (step s i).
Proof.
  destruct (MulDivStall.MulDivStall.done_registers (P.state s) (P.inputs i) (or_intror state) reset kill ready) as [next [select rem]].
  rewrite <-P.step_projects in select,rem.
  change (r6_nresHi (step s i)=word 1 (r6_nresHi s)) in select.
  change (r8_nremainder (step s i)=word 130 (r8_nremainder s)) in rem.
  assert (busy : word 3 (r0_nstate s)<>0) by lia.
  pose proof (D.flag_hold s i busy ltac:(lia) reset) as flag.
  destruct (captured_congruent (step s i) s (MulDivCheckedHistory.MulDivCheckedHistory.hold s i (or_introl busy))) as [extra [negative latency]].
  assert (chosenHold : chosen (step s i)=chosen s).
  { unfold chosen; rewrite (hi_hold s i busy),(W.hold s i state reset kill ready); reflexivity. }
  unfold ResultRelation in *; rewrite select,flag,negative,(hi_hold s i busy),rem,chosenHold.
  rewrite normalize,narrow by lia; exact relation.
Qed.
End MulDivCheckedDivisionOutputControl.
Print Assumptions MulDivCheckedDivisionOutputControl.high_after_reset.
Print Assumptions MulDivCheckedDivisionOutputControl.hold_relation.
