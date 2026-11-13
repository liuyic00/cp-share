From Coq Require Import ZArith Lia.
From Proofs Require Import Words LeadingBits RadixControl RadixBalance RadixLeadingMerge RadixLeadingTree.
From Generated Require Import Radix2Divider.
Import Radix2Divider.CIRCTBits Radix2Divider.nRadix2Divider.
Import LeadingBits.LeadingBits RadixControl.RadixControl RadixBalance.RadixBalance RadixLeadingMerge.RadixLeadingMerge RadixLeadingTree.RadixLeadingTree.
Open Scope Z_scope.
Module RadixLeading.
Theorem divisor_encoder s i : Encodes (word 64 (r5_nbReg s)) (v224 s i).
Proof.
  destruct (correct_146 s i) as [hh rh]; destruct (correct_222 s i) as [hl rl].
  assert (wire : v224 s i = combine 32 (chunk 32 32 (word 64 (r5_nbReg s))) (v146 s i) (v222 s i)).
  { unfold v224, v223, v65, v63, v64, v26.
    change (word 1 0) with 0; change (word 32 0) with 0; rewrite Z.shiftl_0_l, Z.add_0_l.
    exact (merge_wire 5 7 (chunk 32 32 (word 64 (r5_nbReg s))) (v146 s i) (v222 s i) ltac:(lia) ltac:(vm_compute; discriminate) rh rl). }
  pose proof (chunk_merge_correct 32 0 (word 64 (r5_nbReg s)) (v146 s i) (v222 s i) ltac:(lia) hh hl) as h.
  change (Encodes (word 64 (Z.shiftr (word 64 (r5_nbReg s)) 0)) (combine 32 (chunk 32 32 (word 64 (r5_nbReg s))) (v146 s i) (v222 s i))) in h.
  rewrite Z.shiftr_0_r, normalize in h by lia; rewrite wire; exact h.
Qed.
Lemma top_bit_div s i : v227 s i = word 65 (r6_naValx2Reg s) / base.
Proof.
  unfold v227; rewrite Z.shiftr_div_pow2 by lia; apply small.
  pose proof (bounds 65 (r6_naValx2Reg s) ltac:(lia)) as h.
  change (0 <= word 65 (r6_naValx2Reg s) < 36893488147419103232) in h.
  change (0 <= word 65 (r6_naValx2Reg s)/18446744073709551616 < 2).
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
Theorem dividend_encoder s i : Encodes (word 65 (r6_naValx2Reg s)) (v385 s i).
Proof.
  destruct (correct_383 s i) as [hl rl].
  unfold chunk in hl; rewrite Z.shiftr_0_r in hl.
  assert (hb : v227 s i = 0 \/ v227 s i = 1) by (unfold v227; apply Words.bit_cases).
  pose proof (bounds 65 (r6_naValx2Reg s) ltac:(lia)) as ha.
  change (0 <= word 65 (r6_naValx2Reg s) < 36893488147419103232) in ha.
  pose proof (Z.div_mod (word 65 (r6_naValx2Reg s)) base ltac:(unfold base; lia)) as split.
  pose proof (Z.mod_pos_bound (word 65 (r6_naValx2Reg s)) base ltac:(unfold base; lia)) as rem.
  rewrite <- (top_bit_div s i) in split.
  unfold v385, v384, v62; change (word 6 0) with 0.
  destruct hb as [hb|hb]; rewrite hb.
  - change (Encodes (word 65 (r6_naValx2Reg s)) (word 7 (word 6 (v383 s i)))).
    rewrite (small 6) by exact rl.
    rewrite (small 7) by (change (0 <= v383 s i < 128); lia).
    rewrite hb in split.
    assert (same : word 65 (r6_naValx2Reg s) = word 64 (word 65 (r6_naValx2Reg s))).
    { change (word 65 (r6_naValx2Reg s) = word 65 (r6_naValx2Reg s) mod base); lia. }
    rewrite same; exact hl.
  - change (Encodes (word 65 (r6_naValx2Reg s)) 64).
    rewrite hb in split; unfold Encodes; split; [lia | split; [exact ha |]].
    intros _; change (18446744073709551616 <= word 65 (r6_naValx2Reg s)); unfold base in *; lia.
Qed.
End RadixLeading.
Print Assumptions RadixLeading.divisor_encoder.
Print Assumptions RadixLeading.dividend_encoder.
