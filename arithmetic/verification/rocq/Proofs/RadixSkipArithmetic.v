From Coq Require Import ZArith Lia.
From Proofs Require Import Words RadixControl RadixBalance RadixSetup.
From Generated Require Import Radix2Divider.
Import Radix2Divider.CIRCTBits Radix2Divider.nRadix2Divider.
Import RadixControl.RadixControl RadixBalance.RadixBalance RadixSetup.RadixSetup.
Open Scope Z_scope.
Module RadixSkipArithmetic.
Definition skip lb la := Z.min 63 (64+lb-la).
Lemma skip_range lb la (hb : 0 <= lb <= 63) (ha : 0 <= la <= 64) :
  0 <= skip lb la <= 63.
Proof. unfold skip; lia. Qed.
Lemma skip_bound a d lb la (hb : 0 <= lb <= 63) (ha : 0 <= la <= 64)
  (lower : 2^lb <= d) (upper : 0 <= a < 2^(la+1)) :
  a * 2^(skip lb la) / 2^64 < 2*d.
Proof.
  pose proof (skip_range lb la hb ha) as hc.
  assert (hpower : 0 < 2^(skip lb la)) by (apply Z.pow_pos_nonneg; lia).
  assert (he : la+1+skip lb la <= 65+lb) by (unfold skip; lia).
  assert (hprod : a*2^(skip lb la) < 2^(65+lb)).
  { assert (h : a*2^(skip lb la) < 2^(la+1)*2^(skip lb la)) by nia.
    rewrite <- Z.pow_add_r in h by lia.
    eapply Z.lt_le_trans; [exact h | apply Z.pow_le_mono_r; lia]. }
  apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia |].
  rewrite Z.pow_add_r in hprod by lia.
  change (a*2^(skip lb la) < 18446744073709551616*(2*d)).
  change (a*2^(skip lb la) < 36893488147419103232*2^lb) in hprod; nia.
Qed.
(* The saturation and subtraction at the actual skip-count output. The
   bounds on the two encoder outputs are discharged separately. *)
Lemma skip_wire s i (hb : 0 <= v224 s i <= 63) (ha : 0 <= v385 s i <= 64) :
  v390 s i = skip (v224 s i) (v385 s i).
Proof.
  assert (sum : v226 s i = v224 s i + 64).
  { unfold v226, v225; change (word 7 64) with 64; apply small.
    change (0 <= v224 s i + 64 < 128); lia. }
  assert (diff : v386 s i = 64+v224 s i-v385 s i).
  { unfold v386; rewrite sum; rewrite small; [ring | change (0 <= v224 s i+64-v385 s i < 128); lia]. }
  unfold v390, v389, v388, v387, v9; rewrite diff.
  change (word 7 62) with 62; change (word 6 63) with 63.
  rewrite Z.shiftr_0_r.
  destruct (62 <? 64+v224 s i-v385 s i) eqn:h.
  - apply Z.ltb_lt in h; change (63 = skip (v224 s i) (v385 s i)); unfold skip; lia.
  - apply Z.ltb_ge in h.
    change (word 6 (word 6 (64+v224 s i-v385 s i)) = skip (v224 s i) (v385 s i)).
    rewrite normalize by lia; rewrite small.
    + unfold skip; lia.
    + change (0 <= 64+v224 s i-v385 s i < 64); lia.
Qed.
Lemma log2_skip_count s i (hs : word 3 (r0_nstate s) = 1)
  (hr : word 1 (nreset i) = 0) (flag : word 1 (r1_ndivBy0Reg s) = 0)
  (hb : 0 <= v224 s i <= 63) (ha : 0 <= v385 s i <= 64) :
  r9_ncnt_5Fvalue (step s i) = skip (v224 s i) (v385 s i).
Proof.
  assert (h2 : v2 s i = 0) by (apply busy_no_accept; lia).
  assert (h4 : v4 s i = 1) by (unfold v4, v3; rewrite hs; reflexivity).
  cbn [step r9_ncnt_5Fvalue]; rewrite hr.
  unfold v398, v397, v391; rewrite h2, h4, flag.
  change (word 6 (word 6 (word 6 (v390 s i))) = skip (v224 s i) (v385 s i)).
  rewrite (skip_wire s i hb ha); repeat rewrite normalize by lia.
  apply small; pose proof (skip_range (v224 s i) (v385 s i) hb ha).
  change (0 <= skip (v224 s i) (v385 s i) < 64); lia.
Qed.
Lemma divisor_index_range s i : 0 <= v224 s i <= 63.
Proof.
  assert (hbit : v65 s i = 0 \/ v65 s i = 1).
  { unfold v65; destruct (negb (v63 s i =? v64 s i)); [right | left]; reflexivity. }
  assert (hl : 0 <= v223 s i < 32).
  { unfold v223; exact (bounds 5 _ ltac:(lia)). }
  unfold v224, v26; change (word 1 0) with 0; rewrite Z.shiftl_0_l, Z.add_0_l.
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite small.
  - change (0 <= v65 s i*32+v223 s i <= 63); destruct hbit; lia.
  - change (0 <= v65 s i*32+v223 s i < 128); destruct hbit; lia.
Qed.
Lemma dividend_index_range s i : 0 <= v385 s i <= 64.
Proof.
  assert (hbit : v227 s i = 0 \/ v227 s i = 1).
  { unfold v227; apply Words.bit_cases. }
  assert (hl : 0 <= v383 s i < 64).
  { unfold v383; exact (bounds 6 _ ltac:(lia)). }
  unfold v385, v384, v62; change (word 6 0) with 0.
  destruct hbit as [h|h]; rewrite h.
  - change (0 <= word 7 (word 6 (v383 s i)) <= 64).
    rewrite (small 6) by exact hl.
    rewrite (small 7) by (change (0 <= v383 s i < 128); lia); lia.
  - change (0 <= 64 <= 64); lia.
Qed.
Theorem actual_log2_skip_count s i (hs : word 3 (r0_nstate s) = 1)
  (hr : word 1 (nreset i) = 0) (flag : word 1 (r1_ndivBy0Reg s) = 0) :
  r9_ncnt_5Fvalue (step s i) = skip (v224 s i) (v385 s i).
Proof. apply log2_skip_count; auto using divisor_index_range, dividend_index_range. Qed.
End RadixSkipArithmetic.
Print Assumptions RadixSkipArithmetic.skip_bound.
Print Assumptions RadixSkipArithmetic.log2_skip_count.
Print Assumptions RadixSkipArithmetic.actual_log2_skip_count.
