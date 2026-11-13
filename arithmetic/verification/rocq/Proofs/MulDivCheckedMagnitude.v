From Coq Require Import ZArith Lia.
From Proofs Require Import MulDivCheckedLatency MulDivCheckedHistory MulDivSignedCore.
From Generated Require Import MulDivChecked.
Import MulDivChecked.CIRCTBits MulDivChecked.nMulDivChecked
  MulDivCheckedHistory.MulDivCheckedHistory MulDivCheckedLatency.MulDivCheckedLatency.
Open Scope Z_scope.
Module MulDivCheckedMagnitude.
Module P := MulDivCheckedProjection.MulDivCheckedProjection.
Module Core := MulDiv.nMulDiv.
Module T := MulDivTiming.MulDivTiming.
Definition dividend s := v272 s quiet.
Definition divisor s := v216 s quiet.
Definition Correct (s : Core.State) a d :=
  word 64 (Core.r8_nremainder s)=(if d=?0 then 2^64-1 else a/d) /\
  word 64 (Z.shiftr (word 130 (Core.r8_nremainder s)) 65)=a mod d.
Definition remaining s := (65-Z.to_nat (word 7 (r3_ncount s)))%nat.
Definition Computing s := forall pins, T.active pins (remaining s) ->
  Correct (Core.run (P.state s) pins (remaining s)) (dividend s) (divisor s).
Lemma pins_independent s i : v272 s i=dividend s /\ v216 s i=divisor s.
Proof. unfold dividend,divisor,v272,v271; expand_latency; split; reflexivity. Qed.
Lemma parameter_bounds s : 0<=dividend s<2^64 /\ 0<=divisor s<2^64.
Proof. unfold dividend,divisor,v272,v216; split; apply bounds; lia. Qed.
Lemma parameters_hold s i (busy : word 3 (r0_nstate s)<>0) :
  dividend (step s i)=dividend s /\ divisor (step s i)=divisor s.
Proof.
  pose proof (hold s i (or_introl busy)) as history.
  assert (fn : word 4 (r11_ncontractFn (step s i))=word 4 (r11_ncontractFn s)) by exact (f_equal Core.nio_5Freq_5Fbits_5Ffn history).
  assert (dw : word 1 (r12_ncontractDw (step s i))=word 1 (r12_ncontractDw s)) by exact (f_equal Core.nio_5Freq_5Fbits_5Fdw history).
  assert (a : word 64 (r13_ncontractA (step s i))=word 64 (r13_ncontractA s)) by exact (f_equal Core.nio_5Freq_5Fbits_5Fin1 history).
  assert (b : word 64 (r14_ncontractB (step s i))=word 64 (r14_ncontractB s)) by exact (f_equal Core.nio_5Freq_5Fbits_5Fin2 history).
  unfold dividend,divisor,v272,v271; expand_latency; rewrite fn,dw,a,b; split; reflexivity.
Qed.
Theorem initialized_computing s (state : word 3 (r0_nstate s)=3) (count : word 7 (r3_ncount s)=0)
  (dv : word 65 (r7_ndivisor s)=divisor s)
  (initial : MulDivRefinement.MulDivRefinement.packed (P.state s)=dividend s) : Computing s.
Proof.
  unfold Computing,remaining; rewrite count; change (65-Z.to_nat 0)%nat with 65%nat.
  intros pins live; destruct (parameter_bounds s) as [a d].
  assert (an : MulDiv.CIRCTBits.word 64 (dividend s)=dividend s) by (apply Words.word_small; exact a).
  assert (dn : MulDiv.CIRCTBits.word 64 (divisor s)=divisor s) by (apply Words.word_small; exact d).
  pose proof (MulDivSignedCore.MulDivSignedCore.magnitudes (P.state s) pins (dividend s) (divisor s)
    state count ltac:(rewrite dn; exact dv) ltac:(rewrite an; exact initial) live) as result.
  unfold MulDivSignedCore.MulDivSignedCore.quotient in result; rewrite an,dn in result; exact result.
Qed.
Local Opaque Core.run Core.step run step.
Theorem computing_step s i (state : word 3 (r0_nstate s)=3) (count : word 7 (r3_ncount s)<64)
  (reset : word 1 (nreset i)=0) (kill : word 1 (nio_5Fkill i)=0)
  (computing : Computing s) : Computing (step s i).
Proof.
  assert (counter : word 7 (r3_ncount (step s i))=word 7 (r3_ncount s)+1).
  { change (word 7 (Core.r3_ncount (P.state (step s i)))=word 7 (r3_ncount s)+1).
    rewrite P.step_projects,(MulDivControl.MulDivControl.compute_count (P.state s) (P.inputs i) (or_intror state)).
    change (word 7 (word 7 (word 7 (r3_ncount s)+1))=word 7 (r3_ncount s)+1).
    rewrite normalize by lia; apply Words.word_small; pose proof (bounds 7 (r3_ncount s) ltac:(lia)); change (2^7) with 128 in *; lia. }
  assert (rest : remaining s=S (remaining (step s i))).
  { unfold remaining; rewrite counter,Z2Nat.inj_add by (pose proof (bounds 7 (r3_ncount s) ltac:(lia)); lia).
    change (Z.to_nat 1) with 1%nat; assert (small : (Z.to_nat (word 7 (r3_ncount s))<64)%nat) by lia; lia. }
  destruct (parameters_hold s i ltac:(lia)) as [a d].
  intros pins live.
  set (extended := fun t => match t with O => P.inputs i | S n => pins n end).
  assert (all : T.active extended (remaining s)).
  { intros t bound; destruct t as [|t].
    - split; assumption.
    - apply live; rewrite rest in bound; lia. }
  specialize (computing extended all); rewrite rest in computing.
  rewrite T.run_from_next in computing.
  change (Correct (Core.run (Core.step (P.state s) (P.inputs i)) pins (remaining (step s i))) (dividend s) (divisor s)) in computing.
  rewrite P.step_projects,a,d; exact computing.
Qed.
Theorem computing_last s i (state : word 3 (r0_nstate s)=3) (count : word 7 (r3_ncount s)=64)
  (reset : word 1 (nreset i)=0) (kill : word 1 (nio_5Fkill i)=0) (computing : Computing s) :
  Correct (P.state (step s i)) (dividend (step s i)) (divisor (step s i)).
Proof.
  assert (rest : remaining s=1%nat) by (unfold remaining; rewrite count; reflexivity).
  specialize (computing (fun _ => P.inputs i) ltac:(intros t bound; split; assumption)).
  rewrite rest in computing; change (Correct (Core.step (P.state s) (P.inputs i)) (dividend s) (divisor s)) in computing.
  destruct (parameters_hold s i ltac:(lia)) as [a d]; rewrite P.step_projects,a,d; exact computing.
Qed.
End MulDivCheckedMagnitude.
Print Assumptions MulDivCheckedMagnitude.initialized_computing.
Print Assumptions MulDivCheckedMagnitude.computing_step.
Print Assumptions MulDivCheckedMagnitude.computing_last.
