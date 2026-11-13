From Coq Require Import ZArith Lia.
From Proofs Require Import Words RadixControl RadixDatapath RadixBalance RadixSetup.
From Generated Require Import Radix2Divider.
Import Radix2Divider.CIRCTBits Radix2Divider.nRadix2Divider.
Import RadixControl.RadixControl RadixDatapath.RadixDatapath RadixBalance.RadixBalance RadixSetup.RadixSetup.
Open Scope Z_scope.
Module RadixShift.
Lemma shift_fits a c : 0 <= word 65 a * 2^word 6 c < 2^128.
Proof.
  pose proof (bounds 65 a ltac:(lia)) as ha.
  pose proof (bounds 6 c ltac:(lia)) as hc.
  assert (hp : 0 < 2^word 6 c) by (apply Z.pow_pos_nonneg; lia).
  assert (hl : 2^word 6 c <= 2^63) by (apply Z.pow_le_mono_r; change (0 <= word 6 c < 64) in hc; lia).
  split; [nia |].
  assert (h : word 65 a * 2^word 6 c < 2^65 * 2^63) by nia.
  exact h.
Qed.
Theorem shift_datapath s i (hs : word 3 (r0_nstate s) = 2) :
  r2_nshiftReg (step s i) = word 65 (r6_naValx2Reg s) * 2^word 6 (r9_ncnt_5Fvalue s).
Proof.
  assert (h2 : v2 s i = 0) by (apply busy_no_accept; lia).
  assert (h4 : v4 s i = 0) by (unfold v4, v3; rewrite hs; reflexivity).
  assert (h6 : v6 s i = 1) by (unfold v6, v5; rewrite hs; reflexivity).
  assert (h25 : v25 s i = 0) by (unfold v25; rewrite h2, h4; reflexivity).
  cbn [step r2_nshiftReg]; unfold v44, v43; rewrite h25, h6.
  change (word 129 (word 129 (v32 s i)) = word 65 (r6_naValx2Reg s)*2^word 6 (r9_ncnt_5Fvalue s)).
  unfold v32, v31, v30, v29, v28, v27, v26.
  change (word 63 0) with 0; change (word 122 0) with 0; change (word 1 0) with 0.
  rewrite !Z.shiftl_0_l, !Z.add_0_l.
  rewrite (widen 65 128), (widen 6 128) by lia.
  rewrite Z.shiftl_mul_pow2 by (pose proof (bounds 6 (r9_ncnt_5Fvalue s) ltac:(lia)); lia).
  repeat rewrite normalize by lia.
  rewrite (small 128) by apply shift_fits.
  apply small; pose proof (shift_fits (r6_naValx2Reg s) (r9_ncnt_5Fvalue s)); split; [lia |].
  eapply Z.lt_le_trans; [exact (proj2 H) | apply Z.pow_le_mono_r; lia].
Qed.
Theorem shift_alignment s i n a (hs : word 3 (r0_nstate s) = 2)
  (captured : word 65 (r6_naValx2Reg s) = 2*a)
  (count : word 6 (r9_ncnt_5Fvalue s) + Z.of_nat n = 64) :
  2^Z.of_nat n * word 129 (r2_nshiftReg (step s i)) = 2*base*a.
Proof.
  rewrite shift_datapath by exact hs.
  rewrite small.
  - rewrite captured.
    replace (2^Z.of_nat n*(2*a*2^word 6 (r9_ncnt_5Fvalue s))) with
      ((2^word 6 (r9_ncnt_5Fvalue s)*2^Z.of_nat n)*(2*a)) by ring.
    rewrite <- Z.pow_add_r by (pose proof (bounds 6 (r9_ncnt_5Fvalue s) ltac:(lia)); lia).
    rewrite count; unfold base; ring.
  - pose proof (shift_fits (r6_naValx2Reg s) (r9_ncnt_5Fvalue s)); split; [lia |].
    eapply Z.lt_le_trans; [exact (proj2 H) | apply Z.pow_le_mono_r; lia].
Qed.
Local Opaque step.
Theorem setup_alignment s log shift n a
  (hs : word 3 (r0_nstate s) = 1)
  (hr : word 1 (nreset log) = 0) (hj : word 1 (nreset shift) = 0)
  (captured : word 65 (r6_naValx2Reg s) = 2*a)
  (count : word 6 (r9_ncnt_5Fvalue (step (step s log) shift)) + Z.of_nat n = 64) :
  2^Z.of_nat n * word 129 (r2_nshiftReg (step (step s log) shift)) = 2*base*a.
Proof.
  assert (hstate : word 3 (r0_nstate (step s log)) = 2).
  { rewrite (log2_state s log hr hs); reflexivity. }
  apply shift_alignment; [exact hstate | |].
  - rewrite (log2_dividend s log hs), normalize by lia; exact captured.
  - rewrite (shift_count (step s log) shift hstate hj), normalize in count by lia; exact count.
Qed.
End RadixShift.
Print Assumptions RadixShift.shift_alignment.
Print Assumptions RadixShift.setup_alignment.
