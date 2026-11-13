From Coq Require Import ZArith Lia.
From Proofs Require Import Words RadixControl RadixDatapath.
From Generated Require Import Radix2Divider.
Import Radix2Divider.CIRCTBits Radix2Divider.nRadix2Divider.
Import RadixControl.RadixControl RadixDatapath.RadixDatapath.
Open Scope Z_scope.
Module RadixBalance.
Definition base : Z := 18446744073709551616.
Definition low sh := word 64 sh.
Lemma bounds w x (hw : 0 <= w) : 0 <= word w x < 2^w.
Proof. exact (Words.word_bound w x hw). Qed.
Lemma small w x (h : 0 <= x < 2^w) : word w x = x.
Proof. exact (Words.word_small w x h). Qed.
Lemma candidate_div sh : candidate sh = word 129 sh / base.
Proof.
  unfold candidate; rewrite Z.shiftr_div_pow2 by lia.
  apply small. pose proof (bounds 129 sh ltac:(lia)).
  change (0 <= word 129 sh < 680564733841876926926749214863536422912) in H.
  change (0 <= word 129 sh / 18446744073709551616 < 36893488147419103232).
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
Lemma low_normal sh : low (word 129 sh) = low sh.
Proof.
  pose proof (WordBits.WordBits.extract_normal 129 64 0 sh ltac:(lia) ltac:(lia) ltac:(lia)) as h.
  rewrite !Z.shiftr_0_r in h; exact h.
Qed.
Lemma split_shift sh : word 129 sh = candidate sh * base + low sh.
Proof.
  rewrite candidate_div, <- low_normal. unfold low, word at 3.
  pose proof (Z.div_mod (word 129 sh) base ltac:(unfold base; lia)).
  change (word 129 sh = word 129 sh / base * base + word 129 sh mod base).
  lia.
Qed.
Definition packed r l q := word 129 (2 * (r * base + l) + q).
Lemma packed_exact r l q (hr : 0 <= r < base) (hl : 0 <= l < base)
  (hq : 0 <= q <= 1) : packed r l q = 2*(r*base+l)+q.
Proof. unfold packed; apply small; unfold base in *; change (0 <= 2*(r*18446744073709551616+l)+q < 680564733841876926926749214863536422912); nia. Qed.
Lemma restoring_packed sh d : restoringStep sh d = packed (reducedWord sh d) (low sh) (quotientBit sh d).
Proof.
  unfold restoringStep; rewrite Z.shiftr_0_r.
  change (word 64 (word 129 sh)) with (low (word 129 sh)); rewrite low_normal.
  rewrite !Z.shiftl_mul_pow2 by lia. unfold packed, base.
  f_equal; ring.
Qed.
Lemma digit_bound sh d : 0 <= quotientBit sh d <= 1.
Proof. unfold quotientBit; destruct (Z.leb (word 64 d) (candidate sh)); lia. Qed.
Lemma restoring_exact sh d : restoringStep sh d =
  2 * (reducedWord sh d * base + low sh) + quotientBit sh d.
Proof.
  rewrite restoring_packed; apply packed_exact.
  - exact (bounds 64 _ ltac:(lia)).
  - exact (bounds 64 _ ltac:(lia)).
  - apply digit_bound.
Qed.
Lemma packed_candidate r l q (hr : 0 <= r < base) (hl : 0 <= l < base)
  (hq : 0 <= q <= 1) :
  candidate (packed r l q) = 2*r + l / 9223372036854775808.
Proof.
  rewrite candidate_div.
  unfold packed at 1; rewrite normalize by lia.
  change (packed r l q / base = 2*r + l/9223372036854775808).
  rewrite packed_exact by assumption.
  pose proof (Z.div_mod l 9223372036854775808 ltac:(lia)) as he.
  pose proof (Z.mod_pos_bound l 9223372036854775808 ltac:(lia)) as hm.
  symmetry; apply Z.div_unique with (r := 2*(l mod 9223372036854775808)+q).
  - left; unfold base; lia.
  - unfold base; nia.
Qed.
Theorem compute_preserves_candidate_bound s i
  (hs : word 3 (r0_nstate s) = 3)
  (bound : candidate (r2_nshiftReg s) < 2*word 64 (r5_nbReg s)) :
  candidate (r2_nshiftReg (step s i)) < 2*word 64 (r5_nbReg s).
Proof.
  pose proof (bounds 65 (Z.shiftr (word 129 (r2_nshiftReg s)) 64) ltac:(lia)) as hc.
  change (0 <= candidate (r2_nshiftReg s) < 2^65) in hc.
  pose proof (selected_digit_correct (r2_nshiftReg s) (r5_nbReg s) ltac:(lia) bound) as [hi hr].
  pose proof (bounds 64 (r2_nshiftReg s) ltac:(lia)) as hl.
  change (0 <= low (r2_nshiftReg s) < base) in hl.
  rewrite compute_datapath by exact hs; rewrite restoring_packed, packed_candidate.
  - assert (low (r2_nshiftReg s) / 9223372036854775808 < 2).
    { apply Z.div_lt_upper_bound; unfold base in hl; lia. }
    lia.
  - exact (bounds 64 _ ltac:(lia)).
  - exact hl.
  - apply digit_bound.
Qed.
Theorem restoringStep_balance sh d (bound : candidate sh < 2 * word 64 d) :
  restoringStep sh d + 2*base*word 64 d*quotientBit sh d =
  2*word 129 sh + quotientBit sh d.
Proof.
  pose proof (bounds 65 (Z.shiftr (word 129 sh) 64) ltac:(lia)) as hc.
  change (0 <= candidate sh < 2^65) in hc.
  pose proof (selected_digit_correct sh d ltac:(lia) bound) as [hi hr].
  rewrite restoring_exact, split_shift. nia.
Qed.
Theorem compute_preserves_balance s i q scaled
  (hs : word 3 (r0_nstate s) = 3)
  (bound : candidate (r2_nshiftReg s) < 2*word 64 (r5_nbReg s))
  (balance : word 129 (r2_nshiftReg s) + 2*base*word 64 (r5_nbReg s)*q = scaled+q) :
  r2_nshiftReg (step s i) + 2*base*word 64 (r5_nbReg s)*
    (2*q+quotientBit (r2_nshiftReg s) (r5_nbReg s)) =
  2*scaled+(2*q+quotientBit (r2_nshiftReg s) (r5_nbReg s)).
Proof.
  rewrite compute_datapath by exact hs.
  pose proof (restoringStep_balance (r2_nshiftReg s) (r5_nbReg s) bound).
  nia.
Qed.
End RadixBalance.
Print Assumptions RadixBalance.compute_preserves_balance.
Print Assumptions RadixBalance.compute_preserves_candidate_bound.
