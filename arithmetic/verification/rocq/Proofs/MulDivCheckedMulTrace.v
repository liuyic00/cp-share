From Coq Require Import ZArith Lia.
From Proofs Require Import MulDivCheckedMulFuture MulDivCheckedMulTiming MulDivCheckedMetadata MulDivCheckedSignedTimingTrace.
From Generated Require Import MulDivChecked.
Import MulDivChecked.CIRCTBits MulDivChecked.nMulDivChecked
  MulDivCheckedHistory.MulDivCheckedHistory MulDivCheckedAge.MulDivCheckedAge
  MulDivCheckedMulFuture.MulDivCheckedMulFuture.
Open Scope Z_scope.
Module MulDivCheckedMulTrace.
Definition Phases s :=
  (word 3 (r0_nstate s)=2 /\ word 7 (r3_ncount s)<64 /\ Computing s) \/
  (word 3 (r0_nstate s)=6 /\ forall i, nio_5Fresp_5Fbits_5Fdata (observe s i)=M.specification (captured s)).
Definition Invariant s := word 1 (r9_ncontractPending s)=1 -> word 4 (r11_ncontractFn s)<4 -> Phases s.
Lemma capture_enabled s i (accepted : v2 s i=1) (reset : word 1 (nreset i)=0)
  (pending : word 1 (r9_ncontractPending (step s i))=1) : v160 s i=1.
Proof.
  cbn [step r9_ncontractPending] in pending; rewrite reset in pending; unfold v163 in pending; rewrite accepted in pending;
    cbn [Z.eqb Pos.eqb] in pending; unfold v160 in *; repeat rewrite normalize in pending by lia; exact pending.
Qed.
Lemma enabled_kill s i (enabled : v160 s i=1) : word 1 (nio_5Fkill i)=0.
Proof.
  destruct (bit_cases (nio_5Fkill i)) as [kill|kill]; [exact kill|].
  unfold v160,v159,v31 in enabled; rewrite kill in enabled.
  change (word 1 (Z.land (Z.land (v153 s i) (v158 s i)) 0)=1) in enabled;
    rewrite Z.land_0_r in enabled; discriminate.
Qed.
Lemma capture_phase s i (accepted : v2 s i=1) (reset : word 1 (nreset i)=0)
  (pending : word 1 (r9_ncontractPending (step s i))=1)
  (operation : word 4 (r11_ncontractFn (step s i))<4) : Phases (step s i).
Proof.
  destruct (MulDivCheckedSignedTimingTrace.MulDivCheckedSignedTimingTrace.accepted_idle s i accepted) as [idle valid].
  assert (fn : word 4 (r11_ncontractFn (step s i))=word 4 (nio_5Freq_5Fbits_5Ffn i)).
  { cbn [step r11_ncontractFn]; unfold v169; rewrite accepted; cbn [Z.eqb Pos.eqb]; repeat rewrite normalize by lia; reflexivity. }
  rewrite fn in operation.
  pose proof (capture_enabled s i accepted reset pending) as enabled.
  pose proof (enabled_kill s i enabled) as kill.
  pose proof (MulDivCheckedMetadata.MulDivCheckedMetadata.legal_decode s i enabled) as legal.
  assert (mulLegal : M.Legal (P.inputs i)) by (unfold M.Legal,MulDivCheckedHistory.MulDivCheckedHistory.legal in *; change (word 4 (nio_5Freq_5Fbits_5Ffn i)<4 /\ (word 4 (nio_5Freq_5Fbits_5Ffn i)=0 \/ word 1 (nio_5Freq_5Fbits_5Fdw i)=1)); intuition lia).
  pose proof (MulDivCheckedMulTiming.MulDivCheckedMulTiming.capture_phase s i accepted reset operation) as phase.
  pose proof (capture_age s i idle valid) as age.
  destruct phase as [[state [counter bound]]|[state completed]].
  - left; split; [exact state|]; split.
    + rewrite (capture_count s i accepted operation); destruct (word 1 (nio_5Freq_5Fbits_5Fdw i)=?1); lia.
    + apply capture_computing; assumption.
  - rewrite age in completed; change (word 7 0) with 0 in completed.
    unfold MulDivCheckedTimingChecks.MulDivCheckedTimingChecks.cycles in completed;
      destruct (word 1 (r12_ncontractDw (step s i))=?1); discriminate.
Qed.
Theorem step_invariant s i (previous : Invariant s) : Invariant (step s i).
Proof.
  intros pending operation; destruct (MulDivCheckedControl.MulDivCheckedControl.pending_origin s i pending)
    as [reset [accepted|[absent [old live]]]].
  - apply capture_phase; assumption.
  - rewrite (fn_hold s i absent) in operation.
    assert (kill : word 1 (nio_5Fkill i)=0).
    { apply (MulDivActive.MulDivActive.uncancelled (P.state s) (P.inputs i)); rewrite <-P.node_v40; exact live. }
    destruct (previous old operation) as [[state [count computing]]|[state result]].
    + assert (next : r0_nstate (step s i)=if word 7 (r3_ncount s)=?63 then 6 else 2).
      { change (r0_nstate (step s i)) with (Core.r0_nstate (P.state (step s i))).
        rewrite P.step_projects; apply MulDivControl.MulDivControl.mul_state; assumption. }
      destruct (word 7 (r3_ncount s)=?63) eqn:last.
      * apply Z.eqb_eq in last; right; rewrite next; split; [reflexivity|intro later; apply computing_last; assumption].
      * apply Z.eqb_neq in last; left; rewrite next; split; [reflexivity|]; split.
        -- change (word 7 (Core.r3_ncount (P.state (step s i)))<64).
           rewrite P.step_projects,(MulDivControl.MulDivControl.compute_count (P.state s) (P.inputs i) (or_introl state)).
           change (word 7 (word 7 (word 7 (r3_ncount s)+1))<64); rewrite normalize by lia.
           assert (normal : word 7 (word 7 (r3_ncount s)+1)=word 7 (r3_ncount s)+1).
           { apply Words.word_small; pose proof (bounds 7 (r3_ncount s) ltac:(lia)); change (2^7) with 128 in *; lia. }
           rewrite normal; lia.
        -- apply computing_step; try assumption; lia.
    + assert (done : MulDiv.CIRCTBits.word 3 (Core.r0_nstate (P.state s))=6 \/ MulDiv.CIRCTBits.word 3 (Core.r0_nstate (P.state s))=7) by (left; exact state).
      assert (corelive : Core.v40 (P.state s) (P.inputs i)=0) by (rewrite <-P.node_v40; exact live).
      pose proof (MulDivActive.MulDivActive.stalled_done _ _ done corelive) as ready.
      destruct (MulDivStall.MulDivStall.done_registers (P.state s) (P.inputs i) done reset kill ready) as [next rest].
      right; split.
      * change (word 3 (Core.r0_nstate (P.state (step s i)))=6).
        rewrite P.step_projects,next; change (word 3 (word 3 (r0_nstate s))=6); rewrite normalize by lia; exact state.
      * intro later; destruct (MulDivStall.MulDivStall.stall_stable (P.state s) (P.inputs i) (P.inputs later) done reset kill ready) as [valid [data tag]].
        rewrite <-P.step_projects,<-P.observe_projects,<-P.observe_projects in data.
        change (nio_5Fresp_5Fbits_5Fdata (observe (step s i) later)=nio_5Fresp_5Fbits_5Fdata (observe s i)) in data.
        assert (busy : word 3 (r0_nstate s)<>0) by lia.
        rewrite data,result,(hold s i (or_introl busy)); reflexivity.
Qed.
Local Opaque run step.
Theorem run_invariant initial resetInput (reset : word 1 (nreset resetInput)=1) pins n : Invariant (run (step initial resetInput) pins n).
Proof.
  induction n as [|n IH].
  - change (Invariant (step initial resetInput)); intros pending operation; destruct (reset_monitors initial resetInput reset) as [flag rest]; rewrite flag in pending; discriminate.
  - change (run (step initial resetInput) pins (S n)) with (step (run (step initial resetInput) pins n) (pins n)); apply step_invariant; exact IH.
Qed.
End MulDivCheckedMulTrace.
Print Assumptions MulDivCheckedMulTrace.run_invariant.
