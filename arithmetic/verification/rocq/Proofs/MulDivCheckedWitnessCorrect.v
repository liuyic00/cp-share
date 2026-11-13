From Coq Require Import ZArith Lia.
From Proofs Require Import MulDivCheckedMagnitude MulDivCheckedWitness MulDivCheckedDivisionChecks.
From Generated Require Import MulDivChecked.
Import MulDivChecked.CIRCTBits MulDivChecked.nMulDivChecked
  MulDivCheckedMagnitude.MulDivCheckedMagnitude MulDivCheckedWitness.MulDivCheckedWitness.
Open Scope Z_scope.
Module MulDivCheckedWitnessCorrect.
Definition Invariant s :=
  fst (selected s)=(if divisor s=?0 then 2^64-1 else dividend s/divisor s) /\
  snd (selected s)=dividend s mod divisor s.
Theorem from_raw s (flag : word 1 (r16_ncontractWasNegated s)=0)
  (correct : Correct (P.state s) (dividend s) (divisor s)) : Invariant s.
Proof. unfold Invariant; rewrite (from_raw s flag); exact correct. Qed.
Theorem negation_preserves s i (state : word 3 (r0_nstate s)=5) (reset : word 1 (nreset i)=0)
  (correct : Correct (P.state s) (dividend s) (divisor s)) : Invariant (step s i).
Proof.
  unfold Invariant; rewrite (capture s i state reset).
  destruct (parameters_hold s i ltac:(lia)) as [a d]; rewrite a,d; exact correct.
Qed.
Theorem done_preserves s i (state : word 3 (r0_nstate s)=7)
  (reset : word 1 (nreset i)=0) (kill : word 1 (nio_5Fkill i)=0)
  (ready : word 1 (nio_5Fresp_5Fready i)=0) (correct : Invariant s) : Invariant (step s i).
Proof.
  unfold Invariant; rewrite (hold s i state reset kill ready).
  destruct (parameters_hold s i ltac:(lia)) as [a d]; rewrite a,d; exact correct.
Qed.
Theorem arithmetic_checks s i (correct : Invariant s) : MulDivCheckedDivisionChecks.MulDivCheckedDivisionChecks.checks s i.
Proof.
  pose proof (f_equal fst (source_nodes s i)) as q.
  pose proof (f_equal snd (source_nodes s i)) as r.
  cbn [fst snd] in q,r.
  destruct correct as [quot rem].
  destruct (pins_independent s i) as [a d].
  apply MulDivCheckedDivisionChecks.MulDivCheckedDivisionChecks.from_witness.
  - rewrite q,quot,a,d; reflexivity.
  - rewrite r,rem,a,d; reflexivity.
Qed.
End MulDivCheckedWitnessCorrect.
Print Assumptions MulDivCheckedWitnessCorrect.arithmetic_checks.
Print Assumptions MulDivCheckedWitnessCorrect.negation_preserves.
