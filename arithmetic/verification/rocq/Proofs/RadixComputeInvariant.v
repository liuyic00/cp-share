From Coq Require Import ZArith Lia.
From Proofs Require Import Words RadixControl RadixTemporal RadixBalance RadixFinishInvariant.
From Generated Require Import Radix2Divider.
Import Radix2Divider.CIRCTBits Radix2Divider.nRadix2Divider.
Import RadixControl.RadixControl RadixTemporal.RadixTemporal RadixBalance.RadixBalance RadixFinishInvariant.RadixFinishInvariant.
Open Scope Z_scope.
Module RadixComputeInvariant.
Definition remaining s := Z.to_nat (64-word 6 (r9_ncnt_5Fvalue s)).
Definition ComputeCorrect s := forall inputs,
  (forall t, (t < remaining s)%nat -> word 1 (nreset (inputs t)) = 0) ->
  MagnitudeCorrect (run s inputs (remaining s)).
Lemma remaining_bound s : (1 <= remaining s <= 64)%nat.
Proof. unfold remaining; pose proof (count_bound s); lia. Qed.
Lemma remaining_succ s i (hs : word 3 (r0_nstate s) = 3)
  (hr : word 1 (nreset i) = 0) (notLast : word 6 (r9_ncnt_5Fvalue s) <> 63) :
  remaining s = S (remaining (step s i)).
Proof.
  unfold remaining; rewrite (compute_count s i hr hs), normalize by lia.
  rewrite (small 6 (word 6 (r9_ncnt_5Fvalue s)+1)) by (pose proof (count_bound s); change (0 <= word 6 (r9_ncnt_5Fvalue s)+1 < 64); lia).
  pose proof (count_bound s); lia.
Qed.
Definition prepend i (inputs : nat -> Inputs) t := match t with O => i | S k => inputs k end.
Local Opaque step run.
Theorem compute_correct_step s i (hs : word 3 (r0_nstate s) = 3)
  (hr : word 1 (nreset i) = 0) (correct : ComputeCorrect s)
  (notLast : word 6 (r9_ncnt_5Fvalue s) <> 63) : ComputeCorrect (step s i).
Proof.
  intros inputs resets.
  pose proof (remaining_succ s i hs hr notLast) as count.
  assert (all : forall t, (t < remaining s)%nat -> word 1 (nreset (prepend i inputs t)) = 0).
  { intros [|t] ht; [exact hr | apply resets; lia]. }
  specialize (correct (prepend i inputs) all).
  rewrite count, run_from_next in correct; exact correct.
Qed.
Theorem compute_correct_last s i (hr : word 1 (nreset i) = 0)
  (correct : ComputeCorrect s) (last : word 6 (r9_ncnt_5Fvalue s) = 63) : MagnitudeCorrect (step s i).
Proof.
  assert (count : remaining s = 1%nat) by (unfold remaining; rewrite last; reflexivity).
  specialize (correct (fun _ => i) ltac:(intros; exact hr)).
  rewrite count, run_from_next in correct.
  change (MagnitudeCorrect (step s i)) in correct; exact correct.
Qed.
End RadixComputeInvariant.
Print Assumptions RadixComputeInvariant.compute_correct_step.
Print Assumptions RadixComputeInvariant.compute_correct_last.
