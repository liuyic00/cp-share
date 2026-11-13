From Coq Require Import ZArith Lia.
From Proofs Require Import Words RadixControl RadixTemporal RadixBalance RadixCapture RadixSetup RadixExecution RadixZeroResult.
From Generated Require Import Radix2Divider.
Import Radix2Divider.CIRCTBits Radix2Divider.nRadix2Divider.
Import RadixControl.RadixControl RadixTemporal.RadixTemporal RadixBalance.RadixBalance
  RadixCapture.RadixCapture RadixSetup.RadixSetup RadixExecution.RadixExecution RadixZeroResult.RadixZeroResult.
Open Scope Z_scope.
Module RadixZeroAccepted.
Lemma captured_operands s t (h : captured s = captured t) :
  word 64 (r5_nbReg s) = word 64 (r5_nbReg t) /\
  word 65 (r6_naValx2Reg s) = word 65 (r6_naValx2Reg t).
Proof. unfold captured in h; inversion h; split; reflexivity. Qed.
Lemma run_three s inputs : run s inputs 3 = step (step (step s (inputs O)) (inputs 1%nat)) (inputs 2%nat).
Proof. reflexivity. Qed.
Local Opaque run step.
Theorem accepted_zero_magnitudes s inputs
  (idle : word 3 (r0_nstate s) = 0)
  (valid : word 1 (nio_5Fin_5Fvalid (inputs O)) = 1)
  (reset : forall t, (t < 67)%nat -> word 1 (nreset (inputs t)) = 0)
  (zero : word 64 (nio_5Fin_5Fbits_5Fsrc_5F1 (inputs O)) = 0) :
  nio_5Fout_5Fvalid (observe (run s inputs 67) (inputs 67%nat)) = 1 /\
  v40 (run s inputs 67) (inputs 67%nat) = base-1 /\
  v402 (run s inputs 67) (inputs 67%nat) = magnitude (nio_5Fin_5Fbits_5Fsrc_5F0 (inputs O)) (nctrl_5Fsign (inputs O)) /\
  captured (run s inputs 67) = captured (step s (inputs O)).
Proof.
  set (c := step s (inputs O)).
  set (u := step (step c (inputs 1%nat)) (inputs 2%nat)).
  set (later := fun t => inputs (t+3)%nat).
  assert (hc : word 3 (r0_nstate c) = 1).
  { unfold c; rewrite (accept_state s (inputs O) (reset O ltac:(lia)) idle valid); reflexivity. }
  destruct (capture_magnitudes s (inputs O) idle valid) as [ha hb].
  assert (hd : r5_nbReg c = 0).
  { unfold c; rewrite hb; apply magnitude_zero; exact zero. }
  assert (hf : word 1 (r1_ndivBy0Reg c) = 1).
  { assert (h : r1_ndivBy0Reg c = 1).
    { apply (proj2 (capture_zero_flag s (inputs O) idle valid)); exact hd. }
    rewrite h; reflexivity. }
  assert (hu : word 3 (r0_nstate u) = 3).
  { unfold u; rewrite shift_state; [reflexivity | apply reset; lia |].
    rewrite (log2_state c (inputs 1%nat) (reset 1%nat ltac:(lia)) hc); reflexivity. }
  pose proof (setup_captured c (inputs 1%nat) (inputs 2%nat) hc (reset 1%nat ltac:(lia))) as kept.
  change (captured u = captured c) in kept.
  destruct (captured_operands u c kept) as [divisor dividend].
  destruct (zero_setup c (inputs 1%nat) (inputs 2%nat) hc hf (reset 1%nat ltac:(lia)) (reset 2%nat ltac:(lia))) as [count loaded].
  change (r9_ncnt_5Fvalue u = 0) in count.
  change (r2_nshiftReg u = word 65 (r6_naValx2Reg c)) in loaded.
  assert (hr : forall t, (t < 64)%nat -> word 1 (nreset (later t)) = 0).
  { intros; unfold later; apply reset; lia. }
  assert (trace : run s inputs 67 = run u later 64).
  { change (run s inputs (64+3) = run u later 64); rewrite run_shift, run_three; reflexivity. }
  destruct (zero_segment_result u later hu ltac:(rewrite count; reflexivity)
    ltac:(rewrite divisor, hd; reflexivity)
    ltac:(rewrite loaded, RadixDatapath.RadixDatapath.widen by lia; symmetry; exact dividend) hr) as [hv [hq hrem]].
  assert (cap : captured (run u later 64) = captured c).
  { rewrite (compute_captured_run 64 u later hu ltac:(rewrite count; reflexivity) hr); exact kept. }
  rewrite trace; change (nio_5Fout_5Fvalid (observe (run u later 64) (later 64%nat)) = 1 /\
    v40 (run u later 64) (later 64%nat) = base-1 /\
    v402 (run u later 64) (later 64%nat) = magnitude (nio_5Fin_5Fbits_5Fsrc_5F0 (inputs O)) (nctrl_5Fsign (inputs O)) /\ captured (run u later 64) = captured c).
  split; [exact hv | split; [exact hq | split; [|exact cap]]].
  rewrite hrem, dividend; unfold c; rewrite ha.
  rewrite small.
  - rewrite Z.mul_comm; apply Z.div_mul; discriminate.
  - pose proof (bounds 64 (if signBit (nio_5Fin_5Fbits_5Fsrc_5F0 (inputs O)) (nctrl_5Fsign (inputs O)) =? 1 then -word 64 (nio_5Fin_5Fbits_5Fsrc_5F0 (inputs O)) else word 64 (nio_5Fin_5Fbits_5Fsrc_5F0 (inputs O))) ltac:(lia)) as h.
    change (0 <= magnitude (nio_5Fin_5Fbits_5Fsrc_5F0 (inputs O)) (nctrl_5Fsign (inputs O)) < 18446744073709551616) in h.
    change (0 <= 2*magnitude (nio_5Fin_5Fbits_5Fsrc_5F0 (inputs O)) (nctrl_5Fsign (inputs O)) < 36893488147419103232); lia.
Qed.
End RadixZeroAccepted.
Print Assumptions RadixZeroAccepted.accepted_zero_magnitudes.
