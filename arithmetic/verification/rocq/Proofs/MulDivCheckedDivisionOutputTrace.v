From Coq Require Import ZArith Lia List Bool.
From Proofs Require Import MulDivCheckedDivisionOutputControl MulDivCheckedDivisionAssertions.
From Generated Require Import MulDivChecked.
Import MulDivChecked.CIRCTBits MulDivChecked.nMulDivChecked
  MulDivCheckedHistory.MulDivCheckedHistory MulDivCheckedAge.MulDivCheckedAge
  MulDivCheckedLatency.MulDivCheckedLatency MulDivCheckedDivisionOutput.MulDivCheckedDivisionOutput
  MulDivCheckedDivisionOutputControl.MulDivCheckedDivisionOutputControl.
Open Scope Z_scope.
Module MulDivCheckedDivisionOutputTrace.
Module D := MulDivCheckedDivisionTrace.MulDivCheckedDivisionTrace.
Module Sign := MulDivCheckedDivisionSign.MulDivCheckedDivisionSign.
Definition ResultPhases s :=
  (word 3 (r0_nstate s)=5 -> word 1 (r6_nresHi s)=hi s /\ word 1 (r16_ncontractWasNegated s)=0 /\ outputExtra s=1) /\
  (word 3 (r0_nstate s)=7 -> ResultRelation s).
Definition Invariant s := word 1 (r9_ncontractPending s)=1 -> D.Operation s -> ResultPhases s.
Lemma unfinished s (state : word 3 (r0_nstate s)=1 \/ word 3 (r0_nstate s)=2 \/ word 3 (r0_nstate s)=3) : ResultPhases s.
Proof. destruct state as [st|[st|st]]; split; intro impossible; rewrite st in impossible; discriminate. Qed.
Lemma last_edge s i (state : word 3 (r0_nstate s)=3) (count : word 7 (r3_ncount s)=64)
  (high : word 1 (r5_nisHi s)=hi s) (flag : word 1 (r16_ncontractWasNegated s)=0)
  (sign : word 1 (r4_nneg_5Fout s)=outputExtra s)
  (reset : word 1 (nreset i)=0) (kill : word 1 (nio_5Fkill i)=0) : ResultPhases (step s i).
Proof.
  destruct (MulDivSignedExecution.MulDivSignedExecution.last_signed_edge (P.state s) (P.inputs i) state count reset kill) as [next select].
  rewrite <-P.step_projects in next,select.
  change (r0_nstate (step s i)=if word 1 (r4_nneg_5Fout s)=?1 then 5 else 7) in next.
  change (r6_nresHi (step s i)=word 1 (r5_nisHi s)) in select.
  assert (busy : word 3 (r0_nstate s)<>0) by lia.
  assert (nextFlag : word 1 (r16_ncontractWasNegated (step s i))=0) by (rewrite (D.flag_hold s i busy ltac:(lia) reset); exact flag).
  assert (nextHi : word 1 (r6_nresHi (step s i))=hi (step s i)).
  { rewrite select,normalize,(hi_hold s i busy) by lia; exact high. }
  destruct (captured_congruent (step s i) s (MulDivCheckedHistory.MulDivCheckedHistory.hold s i (or_introl busy))) as [extra [negative latency]].
  destruct (bit_cases (r4_nneg_5Fout s)) as [neg|neg]; rewrite neg in next; rewrite neg in sign;
    unfold ResultPhases; rewrite next; split; intro st; try discriminate.
  - unfold ResultRelation; left; split; [exact nextHi|]; split; [exact nextFlag|rewrite negative; symmetry; exact sign].
  - split; [exact nextHi|]; split; [exact nextFlag|rewrite negative; symmetry; exact sign].
Qed.
Theorem step_invariant s i (previous : Invariant s) (initialization : D.Invariant s)
  (highs : HighInvariant s) (signs : Sign.SignInvariant s) : Invariant (step s i).
Proof.
  intros pending op; destruct (MulDivCheckedControl.MulDivCheckedControl.pending_origin s i pending)
    as [reset [accepted|[absent [old live]]]].
  - destruct (MulDivCheckedSignedTimingTrace.MulDivCheckedSignedTimingTrace.accepted_idle s i accepted) as [idle valid].
    destruct (MulDivControl.MulDivControl.acceptance (P.state s) (P.inputs i) idle valid reset) as [states counts].
    rewrite <-P.step_projects in states.
    change (r0_nstate (step s i)=2 \/ r0_nstate (step s i)=1 \/ r0_nstate (step s i)=3) in states.
    apply unfinished; destruct states as [st|[st|st]]; rewrite st; [right; left|left|right; right]; reflexivity.
  - assert (oldOp : D.Operation s) by (unfold D.Operation in *; rewrite (fn_hold s i absent) in op; exact op).
    assert (kill : word 1 (nio_5Fkill i)=0).
    { apply (MulDivActive.MulDivActive.uncancelled (P.state s) (P.inputs i)); rewrite <-P.node_v40; exact live. }
    destruct (initialization old oldOp) as [[signed [neg flag]]|[[state [count [flag computing]]]|[[state correct]|[state correct]]]].
    + assert (state : word 3 (r0_nstate s)=1) by exact (proj1 neg).
      assert (next : r0_nstate (step s i)=3).
      { change (r0_nstate (step s i)) with (MulDiv.nMulDiv.r0_nstate (P.state (step s i))).
        rewrite P.step_projects; apply MulDivControl.MulDivControl.negate_inputs_state; assumption. }
      apply unfinished; rewrite next; right; right; reflexivity.
    + destruct (Z.eq_dec (word 7 (r3_ncount s)) 64) as [last|notLast].
      * apply last_edge; try assumption; [apply highs; assumption|exact (proj1 (signs old oldOp) state last)].
      * assert (next : r0_nstate (step s i)=3).
        { change (r0_nstate (step s i)) with (MulDiv.nMulDiv.r0_nstate (P.state (step s i))).
          rewrite P.step_projects,(MulDivControl.MulDivControl.div_state (P.state s) (P.inputs i) state reset kill).
          assert (off : (word 7 (r3_ncount s)=?64)=false) by (apply Z.eqb_neq; exact notLast).
          change (MulDiv.CIRCTBits.word 7 (MulDiv.nMulDiv.r3_ncount (P.state s))) with (word 7 (r3_ncount s)); rewrite off; reflexivity. }
        apply unfinished; rewrite next; right; right; reflexivity.
    + destruct (proj1 (previous old oldOp) state) as [high [flag negative]].
      assert (next : r0_nstate (step s i)=7).
      { change (r0_nstate (step s i)) with (MulDiv.nMulDiv.r0_nstate (P.state (step s i))).
        rewrite P.step_projects; apply MulDivControl.MulDivControl.negate_output_state; assumption. }
      split; [rewrite next; discriminate|intro done; apply negate_relation; assumption].
    + assert (done : MulDiv.CIRCTBits.word 3 (MulDiv.nMulDiv.r0_nstate (P.state s))=6 \/ MulDiv.CIRCTBits.word 3 (MulDiv.nMulDiv.r0_nstate (P.state s))=7) by (right; exact state).
      assert (corelive : MulDiv.nMulDiv.v40 (P.state s) (P.inputs i)=0) by (rewrite <-P.node_v40; exact live).
      pose proof (MulDivActive.MulDivActive.stalled_done _ _ done corelive) as ready.
      destruct (MulDivStall.MulDivStall.done_registers (P.state s) (P.inputs i) done reset kill ready) as [next rest].
      assert (nextState : word 3 (r0_nstate (step s i))=7).
      { change (word 3 (MulDiv.nMulDiv.r0_nstate (P.state (step s i)))=7).
        rewrite P.step_projects,next; change (word 3 (word 3 (r0_nstate s))=7); rewrite normalize by lia; exact state. }
      split; [rewrite nextState; discriminate|intro valid; apply hold_relation; try assumption; exact (proj2 (previous old oldOp) state)].
Qed.
Local Opaque run step.
Theorem run_invariant initial resetInput (reset : word 1 (nreset resetInput)=1) pins n : Invariant (run (step initial resetInput) pins n).
Proof.
  induction n as [|n IH].
  - change (Invariant (step initial resetInput)); intros pending op; destruct (reset_monitors initial resetInput reset) as [flag rest]; rewrite flag in pending; discriminate.
  - change (run (step initial resetInput) pins (S n)) with (step (run (step initial resetInput) pins n) (pins n)).
    apply step_invariant; [exact IH|apply D.run_invariant|apply high_after_reset|apply Sign.signs_after_reset]; exact reset.
Qed.
Theorem data_assertion_after_reset initial resetInput (reset : word 1 (nreset resetInput)=1) pins n
  (operation : D.Operation (run (step initial resetInput) pins n)) :
  nth 3 (assertionChecks (run (step initial resetInput) pins n) (pins n)) false=true.
Proof.
  set (s := run (step initial resetInput) pins n) in *.
  destruct (Z.eq_dec (word 1 (r9_ncontractPending s)) 1) as [pending|inactive].
  2: { apply MulDivCheckedData.MulDivCheckedData.inactive; intuition. }
  destruct (Z.eq_dec (v38 s (pins n)) 1) as [valid|inactive].
  2: { apply MulDivCheckedData.MulDivCheckedData.inactive; intuition. }
  pose proof (D.run_invariant initial resetInput reset pins n pending operation) as phases.
  assert (done : word 3 (r0_nstate s)=7).
  { change (D.Phases s) in phases.
    destruct phases as [[op [neg flag]]|[[state rest]|[[state correct]|[state correct]]]]; [destruct neg as [state rest]| | |exact state];
      unfold v38,v37,v36,v35,v4 in valid; rewrite state in valid; discriminate. }
  assert (division : v191 s (pins n)=1).
  { unfold v191; destruct operation as [fn|[fn|[fn|fn]]]; rewrite fn; reflexivity. }
  destruct (MulDivCheckedMetadata.MulDivCheckedMetadata.run_invariant initial resetInput reset pins n pending) as [tag width].
  apply MulDivCheckedData.MulDivCheckedData.of_correct; apply output_correct; try assumption.
  exact (proj2 (run_invariant initial resetInput reset pins n pending operation) done).
Qed.
End MulDivCheckedDivisionOutputTrace.
Print Assumptions MulDivCheckedDivisionOutputTrace.data_assertion_after_reset.
Print Assumptions MulDivCheckedDivisionOutputTrace.run_invariant.
