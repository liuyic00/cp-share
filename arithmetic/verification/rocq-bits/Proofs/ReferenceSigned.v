From Stdlib Require Import ZArith Lia Zmod.Bits.
From ReferenceProofs Require Import SignedWords Words.
Open Scope Z_scope.
(* The reference integer view agrees with the native signed bitvector value. *)
Lemma signed_refines w (x : bits w) (hw : 1 <= w) :
  SignedWords.signed w (Zmod.unsigned x) = Zmod.signed x.
Proof.
  unfold SignedWords.signed, Words.word.
  rewrite bits.mod_to_Z.
  unfold Zmod.signed.
  pose proof (bits.unsigned_range x ltac:(lia)) as bound.
  rewrite !Z.abs_eq by (try lia; apply Z.pow_nonneg; lia).
  rewrite Z.double_spec.
  pose proof (SignedWords.double_half w hw) as half.
  destruct (Z.ltb_spec (Zmod.unsigned x) (2^(w-1)));
    destruct (Z.ltb_spec (2 * Zmod.unsigned x) (2^w));
    try reflexivity; lia.
Qed.
Print Assumptions signed_refines.
