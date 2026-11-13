(* Shared numeric normalization for checked node equalities. *)
From Stdlib Require Import ZArith Lia List Bool Zmod.Bits.
From BitsProofs Require Import Unsigned BitFacts.
Open Scope Z_scope.
Ltac app_numeric :=
  match goal with |- context[@Zmod.unsigned ?w (@Zmod.app ?n ?m ?a ?b)] =>
    let H := fresh in
    assert (H : @Zmod.unsigned w (@Zmod.app n m a b) =
      Zmod.unsigned a + Zmod.unsigned b * 2^n)
      by exact (Unsigned.app_add n m a b ltac:(lia) ltac:(lia));
    rewrite H; clear H
  end.
Ltac slice_numeric :=
  match goal with |- context[@Zmod.unsigned ?m (@Zmod.slice ?a ?b ?w ?x)] =>
    let H := fresh in
    assert (H : @Zmod.unsigned m (@Zmod.slice a b w x) =
      Z.shiftr (Zmod.unsigned x) a mod 2^(b-a))
      by exact (Unsigned.slice a b w x ltac:(lia));
    rewrite H; clear H
  end.
Ltac normalize_node :=
  repeat first [app_numeric | slice_numeric |
    rewrite Zmod.unsigned_add | rewrite Zmod.unsigned_mul |
    rewrite bits.unsigned_xor | rewrite bits.unsigned_and | rewrite bits.unsigned_or |
    rewrite bits.unsigned_of_Z];
  rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia;
  unfold Zmod.eqb;
  repeat match goal with |- context[@Zmod.unsigned ?m (@Zmod.one ?n)] =>
    let H := fresh in
    assert (H : @Zmod.unsigned m (@Zmod.one n) = 1) by reflexivity;
    rewrite H; clear H
  end;
  repeat match goal with |- context[@Zmod.unsigned ?m ?x] =>
    let m' := eval vm_compute in m in
    first [constr_eq m m'; fail 1 | change (@Zmod.unsigned m x) with (@Zmod.unsigned m' x)]
  end;
  repeat match goal with |- context[Zmod.unsigned (if ?b then _ else _)] => destruct b end;
  repeat rewrite bits.mod_to_Z;
  repeat rewrite Z.mod_mod by (apply Z.pow_nonzero; lia);
  try reflexivity; try (f_equal; lia).
