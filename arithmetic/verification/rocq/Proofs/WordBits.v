From Coq Require Import ZArith Lia Bool.
From Proofs Require Import Words SignedWords.
Open Scope Z_scope.
Module WordBits.

Lemma extract_normal w k shift x (hk : 0 <= k) (hs : 0 <= shift)
  (fits : shift+k <= w) :
  word k (Z.shiftr (word w x) shift) = word k (Z.shiftr x shift).
Proof.
  unfold word; apply Z.bits_inj; intros n.
  destruct (Z_lt_ge_dec n 0) as [neg|pos].
  - rewrite !Z.testbit_neg_r by lia; reflexivity.
  - destruct (Z_lt_ge_dec n k) as [low|high].
    + rewrite !Z.mod_pow2_bits_low by lia.
      rewrite !Z.shiftr_spec by lia.
      rewrite Z.mod_pow2_bits_low by lia; reflexivity.
    + rewrite !Z.mod_pow2_bits_high by lia; reflexivity.
Qed.

Lemma extract_extract w k offset shift x (hk : 0 <= k) (hs : 0 <= shift)
  (fits : shift+k <= w) :
  word k (Z.shiftr (word w (Z.shiftr x offset)) shift) =
  word k (Z.shiftr x (offset+shift)).
Proof. rewrite extract_normal by lia; rewrite Z.shiftr_shiftr by lia; reflexivity. Qed.

Lemma xor_mask w x (hw : 0 <= w) :
  word w (Z.lxor x (2^w-1)) = word w (Z.lnot x).
Proof.
  replace (2^w-1) with (Z.ones w) by (rewrite Z.ones_equiv; lia).
  unfold word; apply Z.bits_inj; intros n.
  destruct (Z_lt_ge_dec n 0) as [neg|pos].
  - rewrite !Z.testbit_neg_r by lia; reflexivity.
  - destruct (Z_lt_ge_dec n w) as [low|high].
    + rewrite !Z.mod_pow2_bits_low by lia.
      rewrite Z.lxor_spec, Z.ones_spec_low, Z.lnot_spec by lia.
      apply Bool.xorb_true_r.
    + rewrite !Z.mod_pow2_bits_high by lia; reflexivity.
Qed.

Lemma signed_complement w x (hw : 1 <= w) :
  signed w (word w (Z.lnot x)) = -signed w x - 1.
Proof.
  assert (encoded : word w (Z.lnot x) = word w (-signed w x-1)).
  { rewrite lnot_as_opp.
    replace (-x-1) with ((-1)*x+(-1)) by ring.
    replace (-signed w x-1) with ((-1)*signed w x+(-1)) by ring.
    rewrite <- (word_affine w (-1) x (-1)) by lia.
    rewrite <- (word_affine w (-1) (signed w x) (-1)) by lia.
    rewrite word_signed by lia; reflexivity. }
  rewrite encoded, signed_normal by lia.
  apply signed_small; [exact hw|].
  pose proof (signed_range w x hw); lia.
Qed.

(* Appending one copy of the sign bit is the same modular value as signed
   extension. This matches the actual 65-to-66-bit concatenations. *)
Lemma extend_one w x (hw : 1 <= w) :
  word (w+1) (2^w * word 1 (Z.shiftr (word w x) (w-1)) + word w x) =
  word (w+1) (signed w x).
Proof.
  rewrite signed_from_bits by exact hw.
  remember (word 1 (Z.shiftr (word w x) (w-1))) as sign.
  replace (2^w*sign + word w x) with
    ((word w x - 2^w*sign) + sign*2^(w+1)).
  - unfold word at 1; rewrite Z.mod_add by (apply Z.pow_nonzero; lia); reflexivity.
  - replace (w+1) with (Z.succ w) by lia.
    rewrite Z.pow_succ_r by lia; ring.
Qed.

Print Assumptions extract_extract.
Print Assumptions xor_mask.
Print Assumptions signed_complement.
Print Assumptions extend_one.


Lemma word_scale w a x (hw : 0 <= w) : word w (a * word w x) = word w (a*x).
Proof. unfold word; apply Z.mul_mod_idemp_r; apply Z.pow_nonzero; lia. Qed.

Lemma extend_twice w x (hw : 1 <= w) :
  word (w+1) (Z.shiftl (word w x) 1) =
  word (w+1) (Z.shiftl (word (w+1) (signed w x)) 1).
Proof.
  rewrite !Z.shiftl_mul_pow2 by lia; change (2^1) with 2.
  rewrite (Z.mul_comm (word (w+1) (signed w x)) 2), word_scale by lia.
  rewrite signed_from_bits by exact hw.
  remember (word 1 (Z.shiftr (word w x) (w-1))) as sign.
  replace (word w x * 2) with
    (2*(word w x - 2^w*sign) + sign*2^(w+1)).
  - unfold word at 1; rewrite Z.mod_add by (apply Z.pow_nonzero; lia); reflexivity.
  - replace (w+1) with (Z.succ w) by lia; rewrite Z.pow_succ_r by lia; ring.
Qed.

Lemma word_complement w x (hw : 0 <= w) :
  word w (Z.lnot (word w x)) = word w (Z.lnot x).
Proof.
  rewrite !lnot_as_opp.
  replace (-word w x-1) with ((-1)*word w x+(-1)) by ring.
  replace (-x-1) with ((-1)*x+(-1)) by ring.
  apply word_affine; exact hw.
Qed.
Print Assumptions extend_twice.
End WordBits.
