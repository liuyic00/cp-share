From Coq Require Import ZArith Lia.
From Proofs Require Import Words RadixControl RadixDatapath RadixBalance RadixExecution.
From Generated Require Import Radix2Divider.
Import Radix2Divider.CIRCTBits Radix2Divider.nRadix2Divider.
Import RadixControl.RadixControl RadixDatapath.RadixDatapath RadixBalance.RadixBalance RadixExecution.RadixExecution.
Open Scope Z_scope.
Module RadixZero.
Definition zeroStep sh := word 129 (2*word 129 sh+1).
Fixpoint zeroRun n sh := match n with O => word 129 sh | S k => zeroStep (zeroRun k sh) end.
Lemma zeroRun_normal n sh : word 129 (zeroRun n sh) = zeroRun n sh.
Proof. destruct n; cbn [zeroRun]; unfold zeroStep; apply normalize; lia. Qed.
Lemma restoring_zero sh d (hd : word 64 d = 0) : restoringStep sh d = zeroStep sh.
Proof.
  assert (hc : 0 <= candidate sh) by (pose proof (bounds 65 (Z.shiftr (word 129 sh) 64) ltac:(lia)); exact (proj1 H)).
  assert (hcmp : (0 <=? candidate sh) = true) by (apply Z.leb_le; exact hc).
  unfold restoringStep, reducedWord, quotientBit; rewrite hd, hcmp, Z.sub_0_r, lowCandidate_mod.
  rewrite !normalize by lia; rewrite Z.shiftr_0_r.
  change (word 64 (word 129 sh)) with (low (word 129 sh)); rewrite low_normal.
  rewrite !Z.shiftl_mul_pow2 by lia.
  unfold zeroStep; rewrite (split_shift sh).
  change (word 129 ((word 64 (candidate sh)*base+low sh)*2+1) = word 129 (2*(candidate sh*base+low sh)+1)).
  unfold word at 1 2 3; unfold base.
  change (((candidate sh mod 18446744073709551616*18446744073709551616+low sh)*2+1) mod 680564733841876926926749214863536422912 = (2*(candidate sh*18446744073709551616+low sh)+1) mod 680564733841876926926749214863536422912).
  pose proof (Z.div_mod (candidate sh) 18446744073709551616 ltac:(lia)) as h.
  replace ((candidate sh mod 18446744073709551616 * 18446744073709551616 + low sh)*2 + 1) with
    (2*(candidate sh*18446744073709551616+low sh)+1 + (- (candidate sh/18446744073709551616))*680564733841876926926749214863536422912) by nia.
  apply Z.mod_add; discriminate.
Qed.
Theorem compute_zero_step s i (hs : word 3 (r0_nstate s) = 3)
  (hd : word 64 (r5_nbReg s) = 0) : r2_nshiftReg (step s i) = zeroStep (r2_nshiftReg s).
Proof. rewrite compute_datapath by exact hs; apply restoring_zero; exact hd. Qed.
Theorem compute_zero_run n s inputs
  (hs : word 3 (r0_nstate s) = 3)
  (remaining : word 6 (r9_ncnt_5Fvalue s) + Z.of_nat n <= 64)
  (reset : forall t, (t < n)%nat -> word 1 (nreset (inputs t)) = 0)
  (zero : word 64 (r5_nbReg s) = 0) :
  word 64 (r5_nbReg (run s inputs n)) = 0 /\
  word 129 (r2_nshiftReg (run s inputs n)) = zeroRun n (r2_nshiftReg s).
Proof.
  induction n as [|n IH].
  - split; [exact zero | reflexivity].
  - destruct (IH ltac:(rewrite Nat2Z.inj_succ in remaining; lia) ltac:(intros; apply reset; lia)) as [hd hi].
    destruct (compute_prefix n s inputs hs ltac:(rewrite Nat2Z.inj_succ in remaining; lia)
      ltac:(intros; apply reset; lia)) as [state count].
    destruct (compute_preserves_captured (run s inputs n) (inputs n) state) as [capt _].
    cbn [run]; split.
    + rewrite capt, normalize, hd by lia; reflexivity.
    + rewrite (compute_zero_step (run s inputs n) (inputs n) state hd).
      unfold zeroStep at 1; rewrite normalize by lia.
      rewrite hi; cbn [zeroRun]; unfold zeroStep; rewrite zeroRun_normal; reflexivity.
Qed.
End RadixZero.
Print Assumptions RadixZero.compute_zero_run.
