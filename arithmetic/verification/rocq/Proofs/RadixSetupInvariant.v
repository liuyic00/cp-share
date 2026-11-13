From Coq Require Import ZArith Lia.
From Proofs Require Import Words RadixControl RadixTemporal RadixBalance RadixCapture RadixAccepted RadixSetup RadixExecution RadixZeroAccepted RadixSetupResult RadixZeroResult RadixFinishInvariant RadixComputeInvariant.
From Generated Require Import Radix2Divider.
Import Radix2Divider.CIRCTBits Radix2Divider.nRadix2Divider.
Import RadixControl.RadixControl RadixTemporal.RadixTemporal RadixBalance.RadixBalance RadixCapture.RadixCapture
  RadixAccepted.RadixAccepted RadixSetup.RadixSetup RadixExecution.RadixExecution RadixZeroAccepted.RadixZeroAccepted
  RadixSetupResult.RadixSetupResult RadixZeroResult.RadixZeroResult RadixFinishInvariant.RadixFinishInvariant RadixComputeInvariant.RadixComputeInvariant.
Open Scope Z_scope.
Module RadixSetupInvariant.
Definition dividend s := word 65 (r6_naValx2Reg s)/2.
Definition CaptureCorrect s :=
  (word 1 (r1_ndivBy0Reg s)=1 <-> word 64 (r5_nbReg s)=0) /\
  word 65 (r6_naValx2Reg s)=2*dividend s.
Lemma dividend_wire s i : v417 s i = dividend s.
Proof.
  unfold v417, dividend; rewrite Z.shiftr_div_pow2 by lia; apply small.
  pose proof (bounds 65 (r6_naValx2Reg s) ltac:(lia)) as h.
  change (0 <= word 65 (r6_naValx2Reg s) < 36893488147419103232) in h.
  change (0 <= word 65 (r6_naValx2Reg s)/2 < 18446744073709551616).
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
Lemma divisor_normal s i : word 64 (r5_nbReg (step s i)) = r5_nbReg (step s i).
Proof. cbn [step r5_nbReg]; unfold v55; apply normalize; lia. Qed.
Theorem capture_invariant s i (hs : word 3 (r0_nstate s)=0)
  (hv : word 1 (nio_5Fin_5Fvalid i)=1) : CaptureCorrect (step s i).
Proof.
  unfold CaptureCorrect; split.
  - rewrite flag_normal, divisor_normal; apply capture_zero_flag; assumption.
  - destruct (capture_magnitudes s i hs hv) as [ha hb].
    unfold dividend; rewrite dividend_normal, ha.
    replace (2*magnitude (nio_5Fin_5Fbits_5Fsrc_5F0 i) (nctrl_5Fsign i)) with
      (magnitude (nio_5Fin_5Fbits_5Fsrc_5F0 i) (nctrl_5Fsign i)*2) by ring.
    rewrite Z.div_mul by discriminate; ring.
Qed.
Lemma magnitude_from_results final source i (kept : captured final=captured source)
  (h : if word 1 (r1_ndivBy0Reg source)=?1 then
    v40 final i=18446744073709551615 /\ v402 final i=dividend source
    else 0<word 64 (r5_nbReg source) /\ v40 final i=dividend source/word 64 (r5_nbReg source) /\ v402 final i=dividend source mod word 64 (r5_nbReg source)) :
  MagnitudeCorrect final.
Proof.
  unfold captured in kept; injection kept as hd ha has hqs hw hh hf.
  change (if word 1 (r1_ndivBy0Reg final)=?1 then v40 final i=18446744073709551615 /\ v402 final i=v417 final i
    else 0<word 64 (r5_nbReg final) /\ v40 final i=v417 final i/word 64 (r5_nbReg final) /\ v402 final i=v417 final i mod word 64 (r5_nbReg final)).
  rewrite dividend_wire; unfold dividend; rewrite hf, hd, ha; exact h.
Qed.
Local Opaque step run.
Theorem setup_segment_correct s log shift inputs
  (hs : word 3 (r0_nstate s)=1)
  (hr : word 1 (nreset log)=0) (hj : word 1 (nreset shift)=0)
  (capturedCorrect : CaptureCorrect s)
  (reset : forall t, (t < remaining (step (step s log) shift))%nat -> word 1 (nreset (inputs t))=0) :
  MagnitudeCorrect (run (step (step s log) shift) inputs (remaining (step (step s log) shift))).
Proof.
  set (u := step (step s log) shift) in *.
  destruct capturedCorrect as [flag doubled].
  assert (count : word 6 (r9_ncnt_5Fvalue u)+Z.of_nat (remaining u)=64).
  { unfold remaining; rewrite Z2Nat.id; pose proof (count_bound u); lia. }
  pose proof (setup_captured s log shift hs hr) as kept.
  change (captured u=captured s) in kept.
  destruct (captured_operands u s kept) as [hd ha].
  destruct (Z.eq_dec (word 64 (r5_nbReg s)) 0) as [zero|nonzero].
  - assert (hf : word 1 (r1_ndivBy0Reg s)=1) by (apply flag; exact zero).
    destruct (zero_setup s log shift hs hf hr hj) as [hc loaded].
    change (r9_ncnt_5Fvalue u=0) in hc.
    change (r2_nshiftReg u=word 65 (r6_naValx2Reg s)) in loaded.
    assert (n : remaining u=64%nat) by (unfold remaining; rewrite hc; reflexivity).
    assert (hu : word 3 (r0_nstate u)=3).
    { unfold u; rewrite shift_state; [reflexivity | exact hj | rewrite (log2_state s log hr hs); reflexivity]. }
    rewrite n in reset |- *.
    destruct (zero_segment_result u inputs hu ltac:(rewrite hc; reflexivity)
      ltac:(rewrite hd, zero; reflexivity)
      ltac:(rewrite loaded, RadixDatapath.RadixDatapath.widen by lia; symmetry; exact ha) reset) as [hv [hq hrem]].
    assert (finalKept : captured (run u inputs 64)=captured s).
    { rewrite (compute_captured_run 64 u inputs hu ltac:(rewrite hc; reflexivity) reset); exact kept. }
    apply (magnitude_from_results _ s (inputs 64%nat) finalKept).
    rewrite hf; split; [exact hq | rewrite hrem, ha; reflexivity].
  - assert (hf : word 1 (r1_ndivBy0Reg s)=0).
    { destruct (Words.bit_cases (r1_ndivBy0Reg s)) as [h|h]; [exact h |].
      apply flag in h; contradiction. }
    destruct (setup_computes s log shift inputs (dividend s) (remaining u) hs hr hj nonzero hf doubled count reset) as [hv [hq [hrem finalKept]]].
    apply (magnitude_from_results _ s (inputs (remaining u)) finalKept).
    rewrite hf; split; [pose proof (bounds 64 (r5_nbReg s) ltac:(lia)); lia | auto].
Qed.
End RadixSetupInvariant.
Print Assumptions RadixSetupInvariant.capture_invariant.
Print Assumptions RadixSetupInvariant.setup_segment_correct.
