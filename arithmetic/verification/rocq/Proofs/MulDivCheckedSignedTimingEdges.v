From Coq Require Import ZArith Lia.
From Proofs Require Import MulDivCheckedSignedTiming MulDivCheckedAge MulDivSignedExecution MulDivCheckedUnsignedTiming.
From Generated Require Import MulDivChecked.
Import MulDivChecked.CIRCTBits MulDivChecked.nMulDivChecked
  MulDivCheckedHistory.MulDivCheckedHistory MulDivCheckedAge.MulDivCheckedAge
  MulDivCheckedLatency.MulDivCheckedLatency MulDivCheckedSignedTiming.MulDivCheckedSignedTiming.
Open Scope Z_scope.
Module MulDivCheckedSignedTimingEdges.
Definition LatePhases s :=
  (word 3 (r0_nstate s)=3 /\ 1<=word 7 (r3_ncount s)<=64 /\
    word 7 (r10_ncontractAge s)=word 7 (r3_ncount s)+inputExtra s /\
    word 1 (r4_nneg_5Fout s)=outputExtra s) \/
  (word 3 (r0_nstate s)=5 /\ word 7 (r10_ncontractAge s)=65+inputExtra s /\ outputExtra s=1) \/
  (word 3 (r0_nstate s)=7 /\ word 7 (r10_ncontractAge s)=latency s).
Lemma timing_projection s (phases : LatePhases s) : TimingPhases s.
Proof. unfold LatePhases,TimingPhases in *; intuition lia. Qed.
Lemma stable s i (state : word 3 (r0_nstate s)<>0) :
  inputExtra (step s i)=inputExtra s /\ outputExtra (step s i)=outputExtra s /\ latency (step s i)=latency s.
Proof. apply captured_congruent; apply hold; left; exact state. Qed.
Lemma age_advance s i (state : word 3 (r0_nstate s)=3 \/ word 3 (r0_nstate s)=5)
  (age : word 7 (r10_ncontractAge s)<=66)
  (pending : word 1 (r9_ncontractPending s)=1) (reset : word 1 (nreset i)=0) :
  word 7 (r10_ncontractAge (step s i))=word 7 (r10_ncontractAge s)+1.
Proof.
  assert (absent : v2 s i=0) by (apply busy; destruct state; lia).
  assert (valid : v38 s i=0) by (apply phase_valid; intuition).
  rewrite (advance s i reset absent pending valid); apply Words.word_small.
  pose proof (bounds 7 (r10_ncontractAge s) ltac:(lia)); change (2^7) with 128 in *; lia.
Qed.
Lemma signed_formula s (operation : Operation s) : latency s=65+inputExtra s+outputExtra s.
Proof. apply division_latency; unfold Operation in operation; intuition. Qed.
Lemma compute_edge s i (operation : Operation s)
  (state : word 3 (r0_nstate s)=3) (count : 1<=word 7 (r3_ncount s)<=64)
  (age : word 7 (r10_ncontractAge s)=word 7 (r3_ncount s)+inputExtra s)
  (negative : word 1 (r4_nneg_5Fout s)=outputExtra s)
  (pending : word 1 (r9_ncontractPending s)=1)
  (reset : word 1 (nreset i)=0) (kill : word 1 (nio_5Fkill i)=0) : LatePhases (step s i).
Proof.
  destruct (extra_bounds s) as [a b].
  destruct (stable s i ltac:(lia)) as [sa [sb sl]].
  pose proof (age_advance s i (or_introl state) ltac:(lia) pending reset) as increment.
  assert (next : r0_nstate (step s i)=if word 7 (r3_ncount s)=?64 then (if outputExtra s=?1 then 5 else 7) else 3).
  { change (r0_nstate (step s i)) with (MulDiv.nMulDiv.r0_nstate (P.state (step s i))).
    rewrite P.step_projects, (MulDivControl.MulDivControl.div_state (P.state s) (P.inputs i) state reset kill).
    change (MulDiv.CIRCTBits.word 1 (MulDiv.nMulDiv.r4_nneg_5Fout (P.state s))) with (word 1 (r4_nneg_5Fout s)); rewrite negative; reflexivity. }
  assert (counter : word 7 (r3_ncount (step s i))=word 7 (r3_ncount s)+1).
  { change (word 7 (MulDiv.nMulDiv.r3_ncount (P.state (step s i)))=word 7 (r3_ncount s)+1).
    rewrite P.step_projects,(MulDivControl.MulDivControl.compute_count (P.state s) (P.inputs i) (or_intror state)).
    change (word 7 (word 7 (word 7 (r3_ncount s)+1))=word 7 (r3_ncount s)+1).
    rewrite normalize by lia; apply Words.word_small; change (0<=word 7 (r3_ncount s)+1<128); lia. }
  assert (neg : word 1 (r4_nneg_5Fout (step s i))=outputExtra s).
  { change (word 1 (MulDiv.nMulDiv.r4_nneg_5Fout (P.state (step s i)))=outputExtra s).
    rewrite P.step_projects,(MulDivSignedExecution.MulDivSignedExecution.later_flag (P.state s) (P.inputs i) state ltac:(change (word 7 (r3_ncount s)<>0); lia)).
    change (word 1 (word 1 (r4_nneg_5Fout s))=outputExtra s); rewrite normalize by lia; exact negative. }
  unfold LatePhases; destruct (word 7 (r3_ncount s)=?64) eqn:last.
  - apply Z.eqb_eq in last; destruct (outputExtra s=?1) eqn:sign.
    + apply Z.eqb_eq in sign; right; left; rewrite next,increment,sa,sb; repeat split; try reflexivity; lia.
    + apply Z.eqb_neq in sign; right; right; rewrite next,increment,sl,(signed_formula s operation); split; [reflexivity|lia].
  - apply Z.eqb_neq in last; left; rewrite next,counter,increment,neg,sa,sb; repeat split; try reflexivity; lia.
Qed.
Lemma negate_edge s i (operation : Operation s)
  (state : word 3 (r0_nstate s)=5) (age : word 7 (r10_ncontractAge s)=65+inputExtra s)
  (negative : outputExtra s=1) (pending : word 1 (r9_ncontractPending s)=1)
  (reset : word 1 (nreset i)=0) (kill : word 1 (nio_5Fkill i)=0) : LatePhases (step s i).
Proof.
  destruct (extra_bounds s) as [a b]; destruct (stable s i ltac:(lia)) as [sa [sb sl]].
  pose proof (age_advance s i (or_intror state) ltac:(lia) pending reset) as increment.
  unfold LatePhases; right; right; split.
  - change (word 3 (MulDiv.nMulDiv.r0_nstate (P.state (step s i)))=7).
    rewrite P.step_projects,(MulDivControl.MulDivControl.negate_output_state (P.state s) (P.inputs i) state reset kill); reflexivity.
  - rewrite increment,sl,(signed_formula s operation); lia.
Qed.
Lemma hold_edge s i (state : word 3 (r0_nstate s)=7)
  (age : word 7 (r10_ncontractAge s)=latency s)
  (reset : word 1 (nreset i)=0) (live : v40 s i=0) : LatePhases (step s i).
Proof.
  assert (absent : v2 s i=0) by (apply busy; lia).
  assert (corelive : MulDiv.nMulDiv.v40 (P.state s) (P.inputs i)=0) by (rewrite <-P.node_v40; exact live).
  pose proof (MulDivActive.MulDivActive.uncancelled _ _ corelive) as kill.
  assert (done : MulDiv.CIRCTBits.word 3 (MulDiv.nMulDiv.r0_nstate (P.state s))=6 \/
    MulDiv.CIRCTBits.word 3 (MulDiv.nMulDiv.r0_nstate (P.state s))=7) by (right; exact state).
  pose proof (MulDivActive.MulDivActive.stalled_done _ _ done corelive) as ready.
  destruct (MulDivStall.MulDivStall.done_registers (P.state s) (P.inputs i) done reset kill ready) as [next rest].
  destruct (stable s i ltac:(lia)) as [sa [sb sl]].
  unfold LatePhases; right; right; split.
  - change (word 3 (MulDiv.nMulDiv.r0_nstate (P.state (step s i)))=7).
    rewrite P.step_projects,next; change (word 3 (word 3 (r0_nstate s))=7); rewrite normalize by lia; exact state.
  - rewrite (hold_done s i reset absent (done_valid s i state)),sl; exact age.
Qed.
Theorem late_edge s i (operation : Operation s) (phases : LatePhases s)
  (pending : word 1 (r9_ncontractPending s)=1)
  (reset : word 1 (nreset i)=0) (live : v40 s i=0) : LatePhases (step s i).
Proof.
  assert (kill : word 1 (nio_5Fkill i)=0).
  { apply (MulDivActive.MulDivActive.uncancelled (P.state s) (P.inputs i)); rewrite <-P.node_v40; exact live. }
  destruct phases as [[state [count [age neg]]]|[[state [age neg]]|[state age]]].
  - apply compute_edge; assumption.
  - apply negate_edge; assumption.
  - apply hold_edge; assumption.
Qed.
End MulDivCheckedSignedTimingEdges.
Print Assumptions MulDivCheckedSignedTimingEdges.late_edge.
