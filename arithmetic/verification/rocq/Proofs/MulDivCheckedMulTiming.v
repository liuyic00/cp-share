From Coq Require Import ZArith Lia List Bool.
From Proofs Require Import MulDivCheckedAge MulDivCheckedTimingChecks MulDivCheckedControl MulDivActive MulDivStall.
From Generated Require Import MulDivChecked.
Import MulDivChecked.CIRCTBits MulDivChecked.nMulDivChecked
  MulDivCheckedAge.MulDivCheckedAge MulDivCheckedTimingChecks.MulDivCheckedTimingChecks.
Open Scope Z_scope.
Module MulDivCheckedMulTiming.
Definition offset s := if word 1 (r12_ncontractDw s)=?1 then 0 else 32.
(* Integer form of Lean's age/counter invariant; all register reads normalized. *)
Definition Invariant s := word 1 (r9_ncontractPending s)=1 ->
  word 4 (r11_ncontractFn s)<4 ->
  (word 3 (r0_nstate s)=2 /\
   word 7 (r3_ncount s)=word 7 (r10_ncontractAge s)+offset s /\
   word 7 (r10_ncontractAge s)<cycles s) \/
  (word 3 (r0_nstate s)=6 /\ word 7 (r10_ncontractAge s)=cycles s).
Theorem timing_assertions s i (invariant : Invariant s)
  (operation : word 4 (r11_ncontractFn s)<4) :
  forallb (fun b=>b) (firstn 2 (assertionChecks s i))=true.
Proof.
  apply sufficient; intro gate;
    destruct (invariant (gate_pending s i gate) operation) as [[state [count age]]|[state age]];
    rewrite multiply_latency by exact operation.
  - lia.
  - lia.
  - rewrite (multiply_valid s i state).
    assert (different : (word 7 (r10_ncontractAge s)=?cycles s)=false) by (apply Z.eqb_neq; lia).
    rewrite different; reflexivity.
  - rewrite (done_valid s i state),age,Z.eqb_refl; reflexivity.
Qed.
Lemma dimensions s : cycles s+offset s=64 /\ 32<=cycles s<=64 /\ 0<=offset s.
Proof. unfold cycles,offset; destruct (word 1 (r12_ncontractDw s)=?1); lia. Qed.
Lemma counter_age_edge s i
  (state : word 3 (r0_nstate s)=2) (reset : word 1 (nreset i)=0)
  (pending : word 1 (r9_ncontractPending s)=1)
  (count : word 7 (r3_ncount s)=word 7 (r10_ncontractAge s)+offset s)
  (age : word 7 (r10_ncontractAge s)<cycles s) :
  word 7 (r3_ncount (step s i))=word 7 (r10_ncontractAge (step s i))+offset (step s i).
Proof.
  destruct (dimensions s) as [sum [range positive]].
  assert (absent : v2 s i=0) by (apply busy; lia).
  assert (counter : r3_ncount (step s i)=word 7 (word 7 (r3_ncount s)+1)).
  { change (r3_ncount (step s i)) with (MulDiv.nMulDiv.r3_ncount (P.state (step s i))).
    rewrite P.step_projects; apply MulDivControl.MulDivControl.compute_count; left; exact state. }
  rewrite counter, (multiply_age s i state reset pending ltac:(lia)).
  unfold offset at 1; rewrite (width_hold s i absent).
  change (word 7 (word 7 (word 7 (r3_ncount s)+1))=word 7 (r10_ncontractAge s)+1+offset s).
  rewrite MulDivCheckedHistory.MulDivCheckedHistory.normalize by lia.
  rewrite count.
  rewrite Words.word_small; [lia|].
  pose proof (MulDivCheckedHistory.MulDivCheckedHistory.bounds 7 (r10_ncontractAge s) ltac:(lia));
    change (2^7) with 128 in *; lia.
Qed.
Definition Phase s :=
  (word 3 (r0_nstate s)=2 /\
   word 7 (r3_ncount s)=word 7 (r10_ncontractAge s)+offset s /\
   word 7 (r10_ncontractAge s)<cycles s) \/
  (word 3 (r0_nstate s)=6 /\ word 7 (r10_ncontractAge s)=cycles s).
Lemma compute_phase s i
  (state : word 3 (r0_nstate s)=2) (reset : word 1 (nreset i)=0)
  (kill : word 1 (nio_5Fkill i)=0)
  (pending : word 1 (r9_ncontractPending s)=1)
  (count : word 7 (r3_ncount s)=word 7 (r10_ncontractAge s)+offset s)
  (age : word 7 (r10_ncontractAge s)<cycles s) : Phase (step s i).
Proof.
  destruct (dimensions s) as [sum [range positive]].
  assert (absent : v2 s i=0) by (apply busy; lia).
  assert (width : cycles (step s i)=cycles s).
  { unfold cycles; rewrite (width_hold s i absent); reflexivity. }
  assert (next : r0_nstate (step s i)=if word 7 (r3_ncount s)=?63 then 6 else 2).
  { change (r0_nstate (step s i)) with (MulDiv.nMulDiv.r0_nstate (P.state (step s i))).
    rewrite P.step_projects; apply MulDivControl.MulDivControl.mul_state; assumption. }
  pose proof (multiply_age s i state reset pending ltac:(lia)) as increment.
  unfold Phase; destruct (word 7 (r3_ncount s)=?63) eqn:last.
  - apply Z.eqb_eq in last; right; rewrite next,increment,width; split; [reflexivity|lia].
  - apply Z.eqb_neq in last; left; rewrite next; split; [reflexivity|].
    split; [apply counter_age_edge; assumption|rewrite increment,width; lia].
Qed.
Lemma capture_phase s i (accepted : v2 s i=1)
  (reset : word 1 (nreset i)=0)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn i)<4) : Phase (step s i).
Proof.
  pose proof (MulDivCheckedHistory.MulDivCheckedHistory.bounds 4 (nio_5Freq_5Fbits_5Ffn i) ltac:(lia)) as range.
  assert (cases : word 4 (nio_5Freq_5Fbits_5Ffn i)=0 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=1 \/
    word 4 (nio_5Freq_5Fbits_5Ffn i)=2 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=3) by lia.
  assert (mul : v6 s i=1).
  { unfold v6,v5,v4,v3; destruct cases as [h|[h|[h|h]]]; rewrite h; reflexivity. }
  unfold Phase; left; cbn [step r0_nstate r3_ncount r10_ncontractAge].
  rewrite reset; unfold v61,v34,v73,v67,v66,v65,v64,v168,v82,v7,v8,v31; rewrite accepted,mul.
  unfold offset,cycles; cbn [step r12_ncontractDw]; unfold v170; rewrite accepted.
  destruct (MulDivCheckedHistory.MulDivCheckedHistory.bit_cases (nio_5Freq_5Fbits_5Fdw i)) as [width|width];
    rewrite width; vm_compute; intuition discriminate.
Qed.
Lemma hold_phase s i (state : word 3 (r0_nstate s)=6)
  (age : word 7 (r10_ncontractAge s)=cycles s)
  (reset : word 1 (nreset i)=0) (live : v40 s i=0) : Phase (step s i).
Proof.
  assert (absent : v2 s i=0) by (apply busy; lia).
  assert (corelive : MulDiv.nMulDiv.v40 (P.state s) (P.inputs i)=0) by (rewrite <-P.node_v40; exact live).
  pose proof (MulDivActive.MulDivActive.uncancelled _ _ corelive) as kill.
  assert (done : MulDiv.CIRCTBits.word 3 (MulDiv.nMulDiv.r0_nstate (P.state s))=6 \/
    MulDiv.CIRCTBits.word 3 (MulDiv.nMulDiv.r0_nstate (P.state s))=7) by (left; exact state).
  pose proof (MulDivActive.MulDivActive.stalled_done _ _ done corelive) as ready.
  destruct (MulDivStall.MulDivStall.done_registers (P.state s) (P.inputs i) done reset kill ready) as [next rest].
  unfold Phase; right; split.
  - change (word 3 (MulDiv.nMulDiv.r0_nstate (P.state (step s i)))=6).
    rewrite P.step_projects,next; change (word 3 (word 3 (r0_nstate s))=6).
    rewrite MulDivCheckedHistory.MulDivCheckedHistory.normalize by lia; exact state.
  - rewrite (hold_done s i reset absent (done_valid s i state)),age.
    unfold cycles; rewrite (width_hold s i absent); reflexivity.
Qed.
Theorem reset_invariant s i (reset : word 1 (nreset i)=1) : Invariant (step s i).
Proof.
  intros pending operation.
  destruct (MulDivCheckedHistory.MulDivCheckedHistory.reset_monitors s i reset) as [flag rest].
  rewrite flag in pending; discriminate.
Qed.
Theorem step_invariant s i (previous : Invariant s) : Invariant (step s i).
Proof.
  intros pending operation; change (Phase (step s i)).
  destruct (MulDivCheckedControl.MulDivCheckedControl.pending_origin s i pending)
    as [reset [accepted|[absent [old live]]]].
  - apply capture_phase; try assumption.
    cbn [step r11_ncontractFn] in operation; unfold v169 in operation; rewrite accepted in operation.
    cbn [Z.eqb Pos.eqb] in operation;
      repeat rewrite MulDivCheckedHistory.MulDivCheckedHistory.normalize in operation by lia; exact operation.
  - rewrite (fn_hold s i absent) in operation.
    destruct (previous old operation) as [[state [count age]]|[state age]].
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
  (operation : word 4 (r11_ncontractFn (run (step initial resetInput) pins n))<4) :
  forallb (fun b=>b) (firstn 2 (assertionChecks (run (step initial resetInput) pins n) (pins n)))=true.
Proof. apply timing_assertions; [apply run_invariant; exact reset|exact operation]. Qed.
End MulDivCheckedMulTiming.
Print Assumptions MulDivCheckedMulTiming.timing_assertions_after_reset.
Print Assumptions MulDivCheckedMulTiming.timing_assertions.
Print Assumptions MulDivCheckedMulTiming.counter_age_edge.
