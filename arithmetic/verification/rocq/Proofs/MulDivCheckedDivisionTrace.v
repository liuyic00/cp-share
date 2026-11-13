From Coq Require Import ZArith Lia.
From Proofs Require Import MulDivCheckedMagnitudeInit MulDivCheckedWitnessCorrect MulDivCheckedSignedTimingTrace.
From Generated Require Import MulDivChecked.
Import MulDivChecked.CIRCTBits MulDivChecked.nMulDivChecked
  MulDivCheckedHistory.MulDivCheckedHistory MulDivCheckedAge.MulDivCheckedAge
  MulDivCheckedMagnitude.MulDivCheckedMagnitude MulDivCheckedMagnitudeInit.MulDivCheckedMagnitudeInit
  MulDivCheckedSignedTimingInit.MulDivCheckedSignedTimingInit.
Open Scope Z_scope.
Module MulDivCheckedDivisionTrace.
Module S := MulDivCheckedSignedTiming.MulDivCheckedSignedTiming.
Module C := MulDivCheckedSignedTimingCapture.MulDivCheckedSignedTimingCapture.
Module W := MulDivCheckedWitnessCorrect.MulDivCheckedWitnessCorrect.
Definition Operation s := word 4 (r11_ncontractFn s)=4 \/ word 4 (r11_ncontractFn s)=5 \/
  word 4 (r11_ncontractFn s)=6 \/ word 4 (r11_ncontractFn s)=7.
Definition Phases s :=
  (S.Operation s /\ Negating s /\ word 1 (r16_ncontractWasNegated s)=0) \/
  (word 3 (r0_nstate s)=3 /\ word 7 (r3_ncount s)<=64 /\ word 1 (r16_ncontractWasNegated s)=0 /\ Computing s) \/
  (word 3 (r0_nstate s)=5 /\ Correct (P.state s) (dividend s) (divisor s)) \/
  (word 3 (r0_nstate s)=7 /\ W.Invariant s).
Definition Invariant s := word 1 (r9_ncontractPending s)=1 -> Operation s -> Phases s.
Lemma flag_capture s i (accepted : v2 s i=1) : word 1 (r16_ncontractWasNegated (step s i))=0.
Proof.
  cbn [step r16_ncontractWasNegated]; destruct (word 1 (nreset i)=?1); [reflexivity|].
  unfold v176,v174,v31; rewrite accepted; change (word 1 (word 1 (Z.land 0 (v175 s i)))=0).
  rewrite Z.land_0_l; reflexivity.
Qed.
Lemma flag_hold s i (busy : word 3 (r0_nstate s)<>0) (notNegating : word 3 (r0_nstate s)<>5)
  (reset : word 1 (nreset i)=0) : word 1 (r16_ncontractWasNegated (step s i))=word 1 (r16_ncontractWasNegated s).
Proof. exact (f_equal (fun p => fst (fst p)) (hold_witness s i notNegating (or_introl busy) reset)). Qed.
Lemma prepared_phase s (op : S.Operation s) (prepared : Prepared s) (flag : word 1 (r16_ncontractWasNegated s)=0) : Phases s.
Proof.
  right; left; pose proof (signed_prepared s op prepared) as computing.
  destruct prepared as [state [count rest]]; split; [exact state|]; split; [lia|]; split; assumption.
Qed.
Lemma capture_phase s i (accepted : v2 s i=1) (reset : word 1 (nreset i)=0) (op : Operation (step s i)) : Phases (step s i).
Proof.
  destruct (MulDivCheckedSignedTimingTrace.MulDivCheckedSignedTimingTrace.accepted_idle s i accepted) as [idle valid].
  destruct (C.capture_values s i idle valid) as [a [b fn]].
  assert (request : word 4 (nio_5Freq_5Fbits_5Ffn i)=4 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=5 \/
    word 4 (nio_5Freq_5Fbits_5Ffn i)=6 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=7) by (unfold Operation in op; rewrite fn in op; exact op).
  assert (cases : (word 4 (nio_5Freq_5Fbits_5Ffn i)=4 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=6) \/
    (word 4 (nio_5Freq_5Fbits_5Ffn i)=5 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=7)) by intuition.
  pose proof (flag_capture s i accepted) as flag.
  destruct cases as [signed|unsigned].
  - assert (signedOp : S.Operation (step s i)) by (unfold S.Operation; rewrite fn; exact signed).
    destruct (C.capture_phase s i idle valid reset signed) as [neg|prepared].
    + left; split; [exact signedOp|]; split; assumption.
    + apply prepared_phase; assumption.
  - destruct (unsigned_capture s i idle valid reset unsigned) as [state [count computing]].
    right; left; split; [exact state|]; split; [lia|]; split; assumption.
Qed.
Theorem reset_invariant s i (reset : word 1 (nreset i)=1) : Invariant (step s i).
Proof. intros pending op; destruct (reset_monitors s i reset) as [flag rest]; rewrite flag in pending; discriminate. Qed.
Theorem step_invariant s i (previous : Invariant s) : Invariant (step s i).
Proof.
  intros pending op.
  destruct (MulDivCheckedControl.MulDivCheckedControl.pending_origin s i pending) as [reset [accepted|[absent [old live]]]].
  - apply capture_phase; assumption.
  - assert (oldOp : Operation s) by (unfold Operation in *; rewrite (fn_hold s i absent) in op; exact op).
    assert (kill : word 1 (nio_5Fkill i)=0).
    { apply (MulDivActive.MulDivActive.uncancelled (P.state s) (P.inputs i)); rewrite <-P.node_v40; exact live. }
    destruct (previous old oldOp) as [[signed [neg flag]]|[[state [count [flag computing]]]|[[state correct]|[state correct]]]].
    + assert (st : word 3 (r0_nstate s)=1) by exact (proj1 neg).
      apply prepared_phase.
      * unfold S.Operation in *; rewrite (fn_hold s i absent); exact signed.
      * apply input_negation_edge; assumption.
      * rewrite flag_hold by (try assumption; lia); exact flag.
    + assert (next : r0_nstate (step s i)=if word 7 (r3_ncount s)=?64 then (if word 1 (r4_nneg_5Fout s)=?1 then 5 else 7) else 3).
      { change (r0_nstate (step s i)) with (Core.r0_nstate (P.state (step s i))).
        rewrite P.step_projects; apply MulDivControl.MulDivControl.div_state; assumption. }
      assert (nextFlag : word 1 (r16_ncontractWasNegated (step s i))=0) by (rewrite flag_hold by (try assumption; lia); exact flag).
      destruct (word 7 (r3_ncount s)=?64) eqn:last.
      * apply Z.eqb_eq in last; pose proof (computing_last s i state last reset kill computing) as correct.
        destruct (word 1 (r4_nneg_5Fout s)=?1).
        -- right; right; left; rewrite next; split; [reflexivity|exact correct].
        -- right; right; right; rewrite next; split; [reflexivity|apply W.from_raw; assumption].
      * apply Z.eqb_neq in last; right; left; rewrite next; split; [reflexivity|].
        split.
        -- change (word 7 (Core.r3_ncount (P.state (step s i)))<=64).
           rewrite P.step_projects,(MulDivControl.MulDivControl.compute_count (P.state s) (P.inputs i) (or_intror state)).
           change (word 7 (word 7 (word 7 (r3_ncount s)+1))<=64); rewrite normalize by lia.
           assert (normal : word 7 (word 7 (r3_ncount s)+1)=word 7 (r3_ncount s)+1).
           { apply Words.word_small; pose proof (bounds 7 (r3_ncount s) ltac:(lia)); change (2^7) with 128 in *; lia. }
           rewrite normal; lia.
        -- split; [exact nextFlag|apply computing_step; try assumption; lia].
    + right; right; right; split.
      * change (word 3 (Core.r0_nstate (P.state (step s i)))=7).
        rewrite P.step_projects,(MulDivControl.MulDivControl.negate_output_state (P.state s) (P.inputs i) state reset kill); reflexivity.
      * apply W.negation_preserves; assumption.
    + assert (done : MulDiv.CIRCTBits.word 3 (Core.r0_nstate (P.state s))=6 \/ MulDiv.CIRCTBits.word 3 (Core.r0_nstate (P.state s))=7) by (right; exact state).
      assert (corelive : Core.v40 (P.state s) (P.inputs i)=0) by (rewrite <-P.node_v40; exact live).
      pose proof (MulDivActive.MulDivActive.stalled_done _ _ done corelive) as ready.
      destruct (MulDivStall.MulDivStall.done_registers (P.state s) (P.inputs i) done reset kill ready) as [next rest].
      right; right; right; split.
      * change (word 3 (Core.r0_nstate (P.state (step s i)))=7).
        rewrite P.step_projects,next; change (word 3 (word 3 (r0_nstate s))=7); rewrite normalize by lia; exact state.
      * apply W.done_preserves; assumption.
Qed.
Local Opaque run step.
Theorem run_invariant initial resetInput (reset : word 1 (nreset resetInput)=1) pins n : Invariant (run (step initial resetInput) pins n).
Proof.
  induction n as [|n IH]; [apply reset_invariant; exact reset|].
  change (run (step initial resetInput) pins (S n)) with (step (run (step initial resetInput) pins n) (pins n)); apply step_invariant; exact IH.
Qed.
End MulDivCheckedDivisionTrace.
Print Assumptions MulDivCheckedDivisionTrace.run_invariant.
