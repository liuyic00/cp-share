From Coq Require Import ZArith Lia.
From Proofs Require Import Words LeadingBits RadixControl RadixBalance RadixDatapath RadixSetup RadixShift RadixSkipArithmetic RadixLeading.
From Generated Require Import Radix2Divider.
Import Radix2Divider.CIRCTBits Radix2Divider.nRadix2Divider.
Import LeadingBits.LeadingBits RadixControl.RadixControl RadixBalance.RadixBalance RadixDatapath.RadixDatapath RadixSetup.RadixSetup RadixShift.RadixShift RadixSkipArithmetic.RadixSkipArithmetic RadixLeading.RadixLeading.
Open Scope Z_scope.
Module RadixInitialization.
Lemma shift_candidate s i (hs : word 3 (r0_nstate s) = 2) :
  candidate (r2_nshiftReg (step s i)) =
  word 65 (r6_naValx2Reg s)*2^word 6 (r9_ncnt_5Fvalue s)/base.
Proof.
  rewrite candidate_div, shift_datapath by exact hs.
  rewrite small; [reflexivity |].
  pose proof (shift_fits (r6_naValx2Reg s) (r9_ncnt_5Fvalue s)); split; [lia |].
  eapply Z.lt_le_trans; [exact (proj2 H) | apply Z.pow_le_mono_r; lia].
Qed.
Local Opaque step.
Theorem skip_initializes_bound s i j
  (hs : word 3 (r0_nstate s) = 1)
  (hr : word 1 (nreset i) = 0)
  (nonzero : word 64 (r5_nbReg s) <> 0)
  (flag : word 1 (r1_ndivBy0Reg s) = 0) :
  candidate (r2_nshiftReg (step (step s i) j)) < 2*word 64 (r5_nbReg s).
Proof.
  assert (hstate : word 3 (r0_nstate (step s i)) = 2).
  { rewrite (log2_state s i hr hs); reflexivity. }
  rewrite (shift_candidate (step s i) j hstate).
  rewrite (log2_dividend s i hs), normalize by lia.
  rewrite (actual_log2_skip_count s i hs hr flag).
  pose proof (divisor_index_range s i) as hb.
  pose proof (dividend_index_range s i) as ha.
  rewrite (small 6 (skip (v224 s i) (v385 s i))) by (pose proof (skip_range (v224 s i) (v385 s i) hb ha); change (0 <= skip (v224 s i) (v385 s i) < 64); lia).
  destruct (divisor_encoder s i) as [_ [_ lower]].
  destruct (dividend_encoder s i) as [_ [upper _]].
  exact (skip_bound (word 65 (r6_naValx2Reg s)) (word 64 (r5_nbReg s)) (v224 s i) (v385 s i) hb ha (lower nonzero) upper).
Qed.
End RadixInitialization.
Print Assumptions RadixInitialization.skip_initializes_bound.
