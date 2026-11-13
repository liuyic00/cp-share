From Coq Require Import ZArith Lia.
From Proofs Require Import Words RadixControl RadixTemporal RadixCapture RadixSetupResult RadixExecution RadixZeroAccepted.
From Generated Require Import Radix2Divider.
Import Radix2Divider.CIRCTBits Radix2Divider.nRadix2Divider.
Import RadixControl.RadixControl RadixTemporal.RadixTemporal RadixCapture.RadixCapture
  RadixSetupResult.RadixSetupResult RadixExecution.RadixExecution RadixZeroAccepted.RadixZeroAccepted.
Open Scope Z_scope.
Module RadixAccepted.
Lemma flag_normal s i : word 1 (r1_ndivBy0Reg (step s i)) = r1_ndivBy0Reg (step s i).
Proof. cbn [step r1_ndivBy0Reg]; unfold v24; apply normalize; lia. Qed.
Lemma dividend_normal s i : word 65 (r6_naValx2Reg (step s i)) = r6_naValx2Reg (step s i).
Proof. cbn [step r6_naValx2Reg]; unfold v59; apply normalize; lia. Qed.
Lemma capture_nonzero s i (hs : word 3 (r0_nstate s) = 0)
  (hv : word 1 (nio_5Fin_5Fvalid i) = 1)
  (nonzero : word 64 (nio_5Fin_5Fbits_5Fsrc_5F1 i) <> 0) :
  word 64 (r5_nbReg (step s i)) <> 0 /\ word 1 (r1_ndivBy0Reg (step s i)) = 0.
Proof.
  destruct (capture_magnitudes s i hs hv) as [ha hb].
  assert (hd : r5_nbReg (step s i) <> 0).
  { rewrite hb; intro h; apply magnitude_zero in h; contradiction. }
  split.
  - rewrite hb; unfold magnitude; rewrite normalize by lia.
    fold (magnitude (nio_5Fin_5Fbits_5Fsrc_5F1 i) (nctrl_5Fsign i)); rewrite <- hb; exact hd.
  - destruct (Words.bit_cases (r1_ndivBy0Reg (step s i))) as [h|h]; [exact h |].
    change (word 1 (r1_ndivBy0Reg (step s i)) = 1) in h.
    rewrite flag_normal in h; apply (proj1 (capture_zero_flag s i hs hv)) in h; contradiction.
Qed.
Local Opaque run step.
Theorem accepted_magnitudes_correct s inputs
  (idle : word 3 (r0_nstate s) = 0)
  (valid : word 1 (nio_5Fin_5Fvalid (inputs O)) = 1)
  (reset : forall t, (t < 67)%nat -> word 1 (nreset (inputs t)) = 0)
  (nonzero : word 64 (nio_5Fin_5Fbits_5Fsrc_5F1 (inputs O)) <> 0) :
  exists n, (4 <= n <= 67)%nat /\
    nio_5Fout_5Fvalid (observe (run s inputs n) (inputs n)) = 1 /\
    v40 (run s inputs n) (inputs n) =
      magnitude (nio_5Fin_5Fbits_5Fsrc_5F0 (inputs O)) (nctrl_5Fsign (inputs O)) /
      magnitude (nio_5Fin_5Fbits_5Fsrc_5F1 (inputs O)) (nctrl_5Fsign (inputs O)) /\
    v402 (run s inputs n) (inputs n) =
      magnitude (nio_5Fin_5Fbits_5Fsrc_5F0 (inputs O)) (nctrl_5Fsign (inputs O)) mod
      magnitude (nio_5Fin_5Fbits_5Fsrc_5F1 (inputs O)) (nctrl_5Fsign (inputs O)) /\
    captured (run s inputs n) = captured (step s (inputs O)).
Proof.
  set (c := step s (inputs O)).
  set (u := step (step c (inputs 1%nat)) (inputs 2%nat)).
  set (later := fun t => inputs (t+3)%nat).
  set (n := Z.to_nat (64-word 6 (r9_ncnt_5Fvalue u))).
  pose proof (count_bound u) as hb.
  assert (hn : Z.of_nat n = 64-word 6 (r9_ncnt_5Fvalue u)).
  { unfold n; rewrite Z2Nat.id; lia. }
  assert (size : (1 <= n <= 64)%nat) by lia.
  assert (hc : word 3 (r0_nstate c) = 1).
  { unfold c; rewrite (accept_state s (inputs O) (reset O ltac:(lia)) idle valid); reflexivity. }
  destruct (capture_nonzero s (inputs O) idle valid nonzero) as [hd hf].
  destruct (capture_magnitudes s (inputs O) idle valid) as [ha hm].
  pose proof (setup_computes c (inputs 1%nat) (inputs 2%nat) later
    (magnitude (nio_5Fin_5Fbits_5Fsrc_5F0 (inputs O)) (nctrl_5Fsign (inputs O))) n
    hc (reset 1%nat ltac:(lia)) (reset 2%nat ltac:(lia)) hd hf
    ltac:(unfold c; rewrite dividend_normal; exact ha)
    ltac:(change (word 6 (r9_ncnt_5Fvalue u)+Z.of_nat n=64); lia)
    ltac:(intros t ht; unfold later; apply reset; lia)) as result.
  change (nio_5Fout_5Fvalid (observe (run u later n) (later n)) = 1 /\
    v40 (run u later n) (later n) = magnitude (nio_5Fin_5Fbits_5Fsrc_5F0 (inputs O)) (nctrl_5Fsign (inputs O))/word 64 (r5_nbReg c) /\
    v402 (run u later n) (later n) = magnitude (nio_5Fin_5Fbits_5Fsrc_5F0 (inputs O)) (nctrl_5Fsign (inputs O)) mod word 64 (r5_nbReg c) /\
    captured (run u later n)=captured c) in result.
  assert (divisor : word 64 (r5_nbReg c) = magnitude (nio_5Fin_5Fbits_5Fsrc_5F1 (inputs O)) (nctrl_5Fsign (inputs O))).
  { unfold c; rewrite hm; unfold magnitude; apply normalize; lia. }
  rewrite divisor in result.
  exists (n+3)%nat; split; [lia |].
  assert (trace : run s inputs (n+3) = run u later n).
  { rewrite run_shift, run_three; reflexivity. }
  rewrite trace; exact result.
Qed.
End RadixAccepted.
Print Assumptions RadixAccepted.accepted_magnitudes_correct.
