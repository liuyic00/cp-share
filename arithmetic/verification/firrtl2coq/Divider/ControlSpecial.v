From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ArithmeticCommon Require Import BitvectorFacts.
From Divider Require Import Stable Representation ScalarOps LeafWords Slices.
Local Open Scope Z_scope.
Lemma control_36_reference s i ghost : to_Zpos (word_36 (encoded_leaves s i ghost)) = Reference.v21 s i.
Proof.
 rewrite scalar_integer_36 scalar_integer_17 leaf_5_integer.
 unfold Reference.v21, Reference.v20, Radix2Divider.CIRCTBits.word.
 change ((if Z.eqb (if Z.eqb (normalize 64 (Reference.nio_5Fin_5Fbits_5Fsrc_5F1 i)) 0 then 1 else 0) 0 then 1 else 0) =
  (if negb (Z.eqb (normalize 64 (Reference.nio_5Fin_5Fbits_5Fsrc_5F1 i)) 0) then 1 else 0) mod 2).
 destruct (Z.eqb (normalize 64 (Reference.nio_5Fin_5Fbits_5Fsrc_5F1 i)) 0); reflexivity.
Qed.
Print Assumptions control_36_reference.

Lemma control_405_reference s i ghost : to_Zpos (word_405 (encoded_leaves s i ghost)) = Reference.v402 s i.
Proof. rewrite slice_405 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v402, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.

Lemma control_425_reference s i ghost : to_Zpos (word_425 (encoded_leaves s i ghost)) = Reference.v417 s i.
Proof. rewrite slice_425 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v417, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.

Lemma control_436_reference s i ghost : to_Zpos (word_436 (encoded_leaves s i ghost)) = Reference.v417 s i.
Proof. rewrite slice_436 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v417, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
