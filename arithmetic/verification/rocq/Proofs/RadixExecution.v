From Coq Require Import ZArith Lia.
From Proofs Require Import Words RadixControl RadixTemporal RadixDatapath RadixBalance.
From Generated Require Import Radix2Divider.
Import Radix2Divider.CIRCTBits Radix2Divider.nRadix2Divider.
Import RadixControl.RadixControl RadixDatapath.RadixDatapath RadixBalance.RadixBalance.
Open Scope Z_scope.
Module RadixExecution.
Theorem compute_prefix n s inputs
  (hs : word 3 (r0_nstate s) = 3)
  (remaining : word 6 (r9_ncnt_5Fvalue s) + Z.of_nat n < 64)
  (reset : forall t, (t < n)%nat -> word 1 (nreset (inputs t)) = 0) :
  word 3 (r0_nstate (run s inputs n)) = 3 /\
  word 6 (r9_ncnt_5Fvalue (run s inputs n)) = word 6 (r9_ncnt_5Fvalue s) + Z.of_nat n.
Proof.
  induction n as [|n IH].
  - cbn [run]; split; [exact hs | lia].
  - destruct (IH ltac:(rewrite Nat2Z.inj_succ in remaining; lia)
      ltac:(intros; apply reset; lia)) as [state count].
    assert (hr : word 1 (nreset (inputs n)) = 0) by (apply reset; lia).
    cbn [run].
    split.
    + rewrite (compute_state _ _ hr state), count.
      assert (heq : (word 6 (r9_ncnt_5Fvalue s) + Z.of_nat n =? 63) = false).
      { apply Z.eqb_neq; rewrite Nat2Z.inj_succ in remaining; lia. }
      rewrite heq; reflexivity.
    + rewrite (compute_count _ _ hr state), normalize by lia.
      rewrite small.
      * rewrite count, Nat2Z.inj_succ; lia.
      * pose proof (RadixTemporal.RadixTemporal.count_bound (run s inputs n)).
        change (0 <= word 6 (r9_ncnt_5Fvalue (run s inputs n)) + 1 < 64).
        rewrite Nat2Z.inj_succ in remaining; lia.
Qed.
Theorem compute_execution n s inputs
  (hs : word 3 (r0_nstate s) = 3)
  (remaining : word 6 (r9_ncnt_5Fvalue s) + Z.of_nat n <= 64)
  (reset : forall t, (t < n)%nat -> word 1 (nreset (inputs t)) = 0)
  (initialBound : candidate (r2_nshiftReg s) < 2*word 64 (r5_nbReg s)) :
  word 64 (r5_nbReg (run s inputs n)) = word 64 (r5_nbReg s) /\
  candidate (r2_nshiftReg (run s inputs n)) < 2*word 64 (r5_nbReg s) /\
  exists q, 0 <= q < 2^Z.of_nat n /\
    word 129 (r2_nshiftReg (run s inputs n)) + 2*base*word 64 (r5_nbReg s)*q =
      2^Z.of_nat n * word 129 (r2_nshiftReg s) + q.
Proof.
  induction n as [|n IH].
  - cbn [run]; split; [reflexivity | split; [exact initialBound |]].
    exists 0; split; [cbn; lia |].
    change (word 129 (r2_nshiftReg s) + 2*base*word 64 (r5_nbReg s)*0 = 1*word 129 (r2_nshiftReg s)+0); ring.
  - destruct (IH ltac:(rewrite Nat2Z.inj_succ in remaining; lia)
      ltac:(intros; apply reset; lia)) as [divisor [bound [q [size balance]]]].
    destruct (compute_prefix n s inputs hs
      ltac:(rewrite Nat2Z.inj_succ in remaining; lia)
      ltac:(intros; apply reset; lia)) as [state count].
    assert (lb : candidate (r2_nshiftReg (run s inputs n)) < 2*word 64 (r5_nbReg (run s inputs n))) by (rewrite divisor; exact bound).
    pose proof (compute_preserves_balance (run s inputs n) (inputs n) q
      (2^Z.of_nat n * word 129 (r2_nshiftReg s)) state lb ltac:(rewrite divisor; exact balance)) as next.
    pose proof (compute_preserves_candidate_bound (run s inputs n) (inputs n) state lb) as nextBound.
    destruct (compute_preserves_captured (run s inputs n) (inputs n) state) as [nextDiv _].
    pose proof (digit_bound (r2_nshiftReg (run s inputs n)) (r5_nbReg (run s inputs n))) as bitBound.
    cbn [run].
    split; [rewrite nextDiv, normalize, divisor by lia; reflexivity |].
    split; [rewrite divisor in nextBound; exact nextBound |].
    exists (2*q+quotientBit (r2_nshiftReg (run s inputs n)) (r5_nbReg (run s inputs n))).
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; split; [lia |].

    assert (normal : word 129 (r2_nshiftReg (step (run s inputs n) (inputs n))) = r2_nshiftReg (step (run s inputs n) (inputs n))).
    { rewrite compute_datapath by exact state; unfold restoringStep; apply normalize; lia. }
    rewrite normal. rewrite divisor in next. nia.
Qed.
(* All captured arithmetic and output-selection state, normalized exactly as
   read by the generated model. *)
Definition captured s :=
  (word 64 (r5_nbReg s), word 65 (r6_naValx2Reg s),
   word 1 (r3_naSignReg s), word 1 (r4_nqSignReg s),
   word 1 (r7_nctrlReg_5FisW s), word 1 (r8_nctrlReg_5FisHi s),
   word 1 (r1_ndivBy0Reg s)).
Lemma compute_captured s i (hs : word 3 (r0_nstate s) = 3) :
  captured (step s i) = captured s.
Proof.
  destruct (compute_preserves_captured s i hs) as [h0 [h1 [h2 [h3 [h4 [h5 h6]]]]]].
  unfold captured; rewrite h0, h1, h2, h3, h4, h5, h6.
  repeat rewrite normalize by lia; reflexivity.
Qed.
Theorem compute_captured_run n s inputs
  (hs : word 3 (r0_nstate s) = 3)
  (remaining : word 6 (r9_ncnt_5Fvalue s) + Z.of_nat n <= 64)
  (reset : forall t, (t < n)%nat -> word 1 (nreset (inputs t)) = 0) :
  captured (run s inputs n) = captured s.
Proof.
  induction n as [|n IH]; [reflexivity |].
  destruct (compute_prefix n s inputs hs
    ltac:(rewrite Nat2Z.inj_succ in remaining; lia)
    ltac:(intros; apply reset; lia)) as [state count].
  change (captured (step (run s inputs n) (inputs n)) = captured s).
  rewrite compute_captured by exact state.
  apply IH; [rewrite Nat2Z.inj_succ in remaining; lia | intros; apply reset; lia].
Qed.
End RadixExecution.
Print Assumptions RadixExecution.compute_execution.
Print Assumptions RadixExecution.compute_captured_run.
