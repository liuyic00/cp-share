From Coq Require Import ZArith Lia.
From Proofs Require Import Words.
Open Scope Z_scope.

Definition signed (w x : Z) : Z :=
  if Z.ltb (word w x) (2^(w-1)) then word w x else word w x - 2^w.
Lemma double_half w (hw : 1 <= w) : 2^w = 2 * 2^(w-1).
Proof.
  replace w with (Z.succ (w-1)) at 1 by lia.
  rewrite Z.pow_succ_r by lia; reflexivity.
Qed.
Lemma signed_range w x (hw : 1 <= w) :
  -(2^(w-1)) <= signed w x < 2^(w-1).
Proof.
  pose proof (word_bound w x ltac:(lia)).
  pose proof (double_half w hw).
  assert (hp : 0 < 2^(w-1)) by (apply Z.pow_pos_nonneg; lia).
  unfold signed; destruct (Z.ltb_spec (word w x) (2^(w-1))); lia.
Qed.
Lemma signed_small w x (hw : 1 <= w)
  (bound : -(2^(w-1)) <= x < 2^(w-1)) : signed w x = x.
Proof.
  pose proof (double_half w hw) as twice.
  assert (hp : 0 < 2^(w-1)) by (apply Z.pow_pos_nonneg; lia).
  destruct (Z_lt_ge_dec x 0) as [neg|pos].
  - assert (encoded : word w x = x + 2^w).
    { unfold word; symmetry; apply Z.mod_unique with (q := -1); [left|]; lia. }
    unfold signed; rewrite encoded.
    destruct (Z.ltb_spec (x+2^w) (2^(w-1))); lia.
  - assert (encoded : word w x = x).
    { apply word_small; lia. }
    unfold signed; rewrite encoded.
    destruct (Z.ltb_spec x (2^(w-1))); lia.
Qed.
Lemma signed_normal w x (hw : 0 <= w) : signed w (word w x) = signed w x.
Proof. unfold signed; rewrite word_idem by lia; reflexivity. Qed.
Lemma word_signed w x (hw : 1 <= w) : word w (signed w x) = word w x.
Proof.
  unfold signed; destruct (Z.ltb (word w x) (2^(w-1))).
  - apply word_idem; lia.
  - unfold word at 1.
    replace (word w x - 2^w) with (word w x + (-1) * 2^w) by ring.
    rewrite Z.mod_add by (apply Z.pow_nonzero; lia).
    apply word_idem; lia.
Qed.
Lemma signed_extend from to x (hf : 1 <= from) (ht : from <= to) :
  signed to (word to (signed from x)) = signed from x.
Proof.
  rewrite signed_normal by lia; apply signed_small; try lia.
  pose proof (signed_range from x hf).
  assert (2^(from-1) <= 2^(to-1)) by (apply Z.pow_le_mono_r; lia).
  lia.
Qed.

Print Assumptions signed_extend.

Lemma word_affine w a x c (hw : 0 <= w) :
  word w (a * word w x + c) = word w (a*x+c).
Proof.
  unfold word.
  assert (nonzero : 2^w <> 0) by (apply Z.pow_nonzero; lia).
  rewrite <- (Z.add_mod_idemp_l (a * (x mod 2^w)) c (2^w)) by assumption.
  rewrite Z.mul_mod_idemp_r by assumption.
  apply Z.add_mod_idemp_l; assumption.
Qed.
Lemma lnot_as_opp x : Z.lnot x = -x-1.
Proof. pose proof (Z.add_lnot_diag x); lia. Qed.

Lemma sign_bit w x (hw : 1 <= w) :
  word 1 (Z.shiftr (word w x) (w-1)) =
    if Z.ltb (word w x) (2^(w-1)) then 0 else 1.
Proof.
  pose proof (word_bound w x ltac:(lia)) as bound.
  pose proof (double_half w hw) as twice.
  assert (positive : 0 < 2^(w-1)) by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.shiftr_div_pow2 by lia.
  unfold word at 1; change (2^1) with 2.
  destruct (Z.ltb_spec (word w x) (2^(w-1))) as [low|high].
  - rewrite Z.div_small by lia; reflexivity.
  - assert (quotient : word w x / 2^(w-1) = 1).
    { symmetry; apply Z.div_unique with (r := word w x - 2^(w-1)); [left|]; lia. }
    rewrite quotient; reflexivity.
Qed.

Lemma signed_from_bits w x (hw : 1 <= w) :
  signed w x = word w x - 2^w * word 1 (Z.shiftr (word w x) (w-1)).
Proof.
  rewrite sign_bit by exact hw; unfold signed.
  destruct (Z.ltb (word w x) (2^(w-1))); ring.
Qed.
Print Assumptions signed_from_bits.
