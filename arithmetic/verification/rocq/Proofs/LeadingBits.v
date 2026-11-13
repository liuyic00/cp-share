From Coq Require Import ZArith Lia.
From Proofs Require Import Words.
Open Scope Z_scope.
Module LeadingBits.
Definition Encodes x k := 0 <= k /\ 0 <= x < 2^(k+1) /\ (x <> 0 -> 2^k <= x).
Definition leaf4 x :=
  if word 1 (Z.shiftr (word 4 x) 3) =? 1 then 3
  else if word 1 (Z.shiftr (word 4 x) 2) =? 1 then 2
  else word 1 (Z.shiftr (word 4 x) 1).
Lemma leaf4_correct x : Encodes (word 4 x) (leaf4 x) /\ 0 <= leaf4 x < 4.
Proof.
  pose proof (word_bound 4 x ltac:(lia)) as h.
  change (0 <= word 4 x < 16) in h.
  assert (cases : word 4 x = 0 \/ word 4 x = 1 \/ word 4 x = 2 \/ word 4 x = 3 \/
    word 4 x = 4 \/ word 4 x = 5 \/ word 4 x = 6 \/ word 4 x = 7 \/
    word 4 x = 8 \/ word 4 x = 9 \/ word 4 x = 10 \/ word 4 x = 11 \/
    word 4 x = 12 \/ word 4 x = 13 \/ word 4 x = 14 \/ word 4 x = 15) by lia.
  unfold leaf4, Encodes.
  repeat destruct cases as [cases|cases]; rewrite cases; vm_compute; intuition discriminate.
Qed.
Definition combine n high hiIndex loIndex := if high =? 0 then loIndex else n+hiIndex.
Lemma combine_correct n hi lo kh kl
  (hn : 0 <= n) (hl : 0 <= lo < 2^n)
  (high : Encodes hi kh) (low : Encodes lo kl) :
  Encodes (hi*2^n+lo) (combine n hi kh kl).
Proof.
  destruct high as [hkh [[hhi hu] hd]].
  destruct low as [hkl [[hlo lu] ld]].
  unfold combine; destruct (hi =? 0) eqn:h.
  - apply Z.eqb_eq in h; subst hi; replace (0*2^n+lo) with lo by ring.
    repeat split; auto.
  - apply Z.eqb_neq in h.
    assert (hp : 0 < 2^n) by (apply Z.pow_pos_nonneg; lia).
    unfold Encodes; split; [lia|]; split.
    + split; [nia |].
      replace (n+kh+1) with ((kh+1)+n) by ring.
      rewrite Z.pow_add_r by lia; nia.
    + intros _; rewrite Z.pow_add_r by lia; specialize (hd h); nia.
Qed.
Lemma combine_range n hi kh kl
  (hn : 0 < n) (hh : 0 <= kh < n) (hl : 0 <= kl < n) :
  0 <= combine n hi kh kl < 2*n.
Proof. unfold combine; destruct (hi =? 0); lia. Qed.
End LeadingBits.
Print Assumptions LeadingBits.combine_correct.
