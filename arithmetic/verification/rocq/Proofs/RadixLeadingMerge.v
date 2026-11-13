From Coq Require Import ZArith Lia.
From Proofs Require Import Words WordBits LeadingBits RadixControl.
From Generated Require Import Radix2Divider.
Import Radix2Divider.CIRCTBits Radix2Divider.nRadix2Divider.
Import RadixControl.RadixControl.
Open Scope Z_scope.
Module RadixLeadingMerge.
Lemma small w x (h : 0 <= x < 2^w) : word w x = x.
Proof. exact (Words.word_small w x h). Qed.
Definition chunk w o x := word w (Z.shiftr x o).
Lemma split_word n x (hn : 0 <= n) :
  word (2*n) x = word n (Z.shiftr x n)*2^n + word n x.
Proof.
  unfold word; rewrite Z.shiftr_div_pow2 by lia.
  replace (2*n) with (n+n) by ring; rewrite Z.pow_add_r by lia.
  rewrite Z.rem_mul_r by (apply Z.pow_nonzero || apply Z.pow_pos_nonneg; lia).
  ring.
Qed.
Lemma chunk_split n o x (hn : 0 <= n) :
  chunk (2*n) o x = chunk n (o+n) x * 2^n + chunk n o x.
Proof.
  unfold chunk; rewrite split_word by exact hn.
  rewrite Z.shiftr_shiftr by lia; reflexivity.
Qed.
Lemma merge_wire k out hi kh kl (hk : 0 <= k)
  (fits : 2*2^k <= 2^out)
  (hh : 0 <= kh < 2^k) (hl : 0 <= kl < 2^k) :
  word out (Z.shiftl (word 1 (if negb (hi =? 0) then 1 else 0)) k +
    word k (if word 1 (if negb (hi =? 0) then 1 else 0) =? 1 then kh else kl)) =
  LeadingBits.LeadingBits.combine (2^k) hi kh kl.
Proof.
  unfold LeadingBits.LeadingBits.combine; destruct (hi =? 0).
  - change (word out (Z.shiftl 0 k + word k kl) = kl).
    rewrite Z.shiftl_0_l, Z.add_0_l.
    rewrite (small k kl hl).
    apply Words.word_small; pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) hk); lia.
  - change (word out (Z.shiftl 1 k + word k kh) = 2^k+kh).
    rewrite Z.shiftl_mul_pow2 by lia; rewrite Z.mul_1_l.
    rewrite (small k kh hh).
    apply Words.word_small; pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) hk); lia.
Qed.
Lemma chunk_merge_correct n o x kh kl (hn : 0 < n)
  (high : LeadingBits.LeadingBits.Encodes (chunk n (o+n) x) kh)
  (low : LeadingBits.LeadingBits.Encodes (chunk n o x) kl) :
  LeadingBits.LeadingBits.Encodes (chunk (2*n) o x)
    (LeadingBits.LeadingBits.combine n (chunk n (o+n) x) kh kl).
Proof.
  rewrite chunk_split by lia; apply LeadingBits.LeadingBits.combine_correct; try assumption; try lia.
  exact (Words.word_bound n (Z.shiftr x o) ltac:(lia)).
Qed.
End RadixLeadingMerge.
Print Assumptions RadixLeadingMerge.chunk_merge_correct.
