From Coq Require Import ZArith Lia List Bool.
From Proofs Require Import MulDivCheckedLatency MulDivCheckedTimingChecks.
From Generated Require Import MulDivChecked.
Import MulDivChecked.CIRCTBits MulDivChecked.nMulDivChecked
  MulDivCheckedLatency.MulDivCheckedLatency MulDivCheckedTimingChecks.MulDivCheckedTimingChecks.
Open Scope Z_scope.
Module MulDivCheckedSignedTiming.
Definition Operation s := word 4 (r11_ncontractFn s)=4 \/ word 4 (r11_ncontractFn s)=6.
(* Timing projection of Lean's five-phase invariant. Establishing it on runs
   also requires the signed datapath facts for capture and zero correction. *)
Definition TimingPhases s :=
  (word 3 (r0_nstate s)=1 /\ word 7 (r10_ncontractAge s)=0) \/
  (word 3 (r0_nstate s)=3 /\ word 7 (r3_ncount s)<=64 /\
    word 7 (r10_ncontractAge s)=word 7 (r3_ncount s)+inputExtra s) \/
  (word 3 (r0_nstate s)=5 /\ word 7 (r10_ncontractAge s)=65+inputExtra s /\ outputExtra s=1) \/
  (word 3 (r0_nstate s)=7 /\ word 7 (r10_ncontractAge s)=latency s).
Lemma phase_valid s i (state : word 3 (r0_nstate s)=1 \/ word 3 (r0_nstate s)=3 \/ word 3 (r0_nstate s)=5) : v38 s i=0.
Proof. unfold v38,v37,v36,v35,v4; destruct state as [st|[st|st]]; rewrite st; reflexivity. Qed.
Lemma done_valid s i (state : word 3 (r0_nstate s)=7) : v38 s i=1.
Proof. unfold v38,v37,v36,v35,v4; rewrite state; reflexivity. Qed.
Lemma phase_conditions s i (operation : Operation s) (phases : TimingPhases s) :
  word 7 (r10_ncontractAge s)<=latency s /\
  v38 s i=(if word 7 (r10_ncontractAge s)=?latency s then 1 else 0).
Proof.
  assert (division : word 4 (r11_ncontractFn s)=4 \/ word 4 (r11_ncontractFn s)=5 \/
    word 4 (r11_ncontractFn s)=6 \/ word 4 (r11_ncontractFn s)=7) by (unfold Operation in operation; intuition).
  pose proof (division_latency s division) as formula.
  destruct (extra_bounds s) as [a b].
  destruct phases as [[state age]|[[state [count age]]|[[state [age neg]]|[state age]]]].
  - rewrite (phase_valid s i (or_introl state)),age; split; [lia|].
    assert (different : (0=?latency s)=false) by (apply Z.eqb_neq; lia); rewrite different; reflexivity.
  - rewrite (phase_valid s i (or_intror (or_introl state))),age; split; [lia|].
    assert (different : (word 7 (r3_ncount s)+inputExtra s=?latency s)=false) by (apply Z.eqb_neq; lia).
    rewrite different; reflexivity.
  - rewrite (phase_valid s i (or_intror (or_intror state))),age; split; [lia|].
    assert (different : (65+inputExtra s=?latency s)=false) by (apply Z.eqb_neq; lia).
    rewrite different; reflexivity.
  - rewrite (done_valid s i state),age,Z.eqb_refl; split; [lia|reflexivity].
Qed.
Theorem timing_assertions s i (operation : Operation s)
  (phases : word 1 (r9_ncontractPending s)=1 -> TimingPhases s) :
  forallb (fun b=>b) (firstn 2 (assertionChecks s i))=true.
Proof.
  apply sufficient; intro gate; rewrite pins_independent;
    destruct (phase_conditions s i operation (phases (gate_pending s i gate))); assumption.
Qed.
End MulDivCheckedSignedTiming.
Print Assumptions MulDivCheckedSignedTiming.timing_assertions.
