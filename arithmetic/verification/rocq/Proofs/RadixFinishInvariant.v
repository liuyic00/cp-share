From Coq Require Import ZArith Lia List Bool.
From Proofs Require Import Words RadixControl RadixSetup RadixExecution RadixArithmeticChecks RadixHistoryChecks.
From Generated Require Import Radix2Divider.
Import Radix2Divider.CIRCTBits Radix2Divider.nRadix2Divider.
Import RadixControl.RadixControl RadixSetup.RadixSetup RadixExecution.RadixExecution
  RadixArithmeticChecks.RadixArithmeticChecks RadixHistoryChecks.RadixHistoryChecks.
Open Scope Z_scope.
Module RadixFinishInvariant.
Definition MagnitudeCorrect s :=
  let q := word 64 (Z.shiftr (word 129 (r2_nshiftReg s)) 0) in
  let r := word 64 (Z.shiftr (word 129 (r2_nshiftReg s)) 65) in
  let a := word 64 (Z.shiftr (word 65 (r6_naValx2Reg s)) 1) in
  let d := word 64 (r5_nbReg s) in
  if word 1 (r1_ndivBy0Reg s) =? 1 then q=18446744073709551615 /\ r=a
  else 0<d /\ q=a/d /\ r=a mod d.
Definition FinishInvariant s := word 3 (r0_nstate s) = 4 -> MagnitudeCorrect s.
Lemma magnitude_correct_checks s i (correct : MagnitudeCorrect s) : arithmeticChecks s i.
Proof.
  change (if word 1 (r1_ndivBy0Reg s) =? 1 then v40 s i=18446744073709551615 /\ v402 s i=v417 s i
    else 0<word 64 (r5_nbReg s) /\ v40 s i=v417 s i/word 64 (r5_nbReg s) /\ v402 s i=v417 s i mod word 64 (r5_nbReg s)) in correct.
  destruct (bit_cases (r1_ndivBy0Reg s)) as [h|h]; rewrite h in correct.
  - destruct correct as [positive [q r]]; apply arithmetic_checks_nonzero; assumption.
  - destruct correct as [q r]; apply arithmetic_checks_zero; assumption.
Qed.
Lemma asserts_after_edge_iff s i j : asserts (step s i) j <-> arithmeticChecks (step s i) j.
Proof.
  unfold asserts, arithmeticChecks.
  pose proof (firstn_skipn 5 (assertionChecks (step s i) j)) as partition.
  rewrite <- partition at 1; rewrite forallb_app, temporal_assertions_step, Bool.andb_true_r; reflexivity.
Qed.
Theorem finish_invariant_asserts s previous i (h : FinishInvariant (step s previous)) : asserts (step s previous) i.
Proof.
  apply asserts_after_edge_iff.
  destruct (Z.eq_dec (word 3 (r0_nstate (step s previous))) 4) as [hs|hs].
  - apply magnitude_correct_checks; apply h; exact hs.
  - apply arithmetic_checks_inactive; left; exact hs.
Qed.
Lemma magnitude_congruent s t (kept : captured s = captured t)
  (shift : word 129 (r2_nshiftReg s) = word 129 (r2_nshiftReg t)) :
  MagnitudeCorrect s <-> MagnitudeCorrect t.
Proof.
  unfold captured in kept; injection kept as hd ha has hqs hw hh hf.
  unfold MagnitudeCorrect; rewrite shift, hd, ha, hf; reflexivity.
Qed.
Theorem finish_preserves_correct s i (hs : word 3 (r0_nstate s) = 4)
  (correct : MagnitudeCorrect s) : MagnitudeCorrect (step s i).
Proof.
  apply (proj2 (magnitude_congruent (step s i) s
    (busy_captured s i ltac:(lia)) (proj1 (finish_registers s i hs)))); exact correct.
Qed.
End RadixFinishInvariant.
Print Assumptions RadixFinishInvariant.finish_invariant_asserts.
Print Assumptions RadixFinishInvariant.finish_preserves_correct.
