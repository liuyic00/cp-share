From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ArithmeticCommon Require Import BitvectorFacts.
From Divider Require Import Stable Representation Controls OutputSign ScalarOps LeafWords.
Local Open Scope Z_scope.
Local Opaque Reference.v412.
Lemma output_418_reference s i ghost : to_Zpos (word_418 (encoded_leaves s i ghost)) = Reference.v412 s i.
Proof. apply output_mux_418_reference. apply control_412_reference. Qed.
Lemma output_9_reference s i ghost : to_Zpos (word_9 (encoded_leaves s i ghost)) = Reference.v412 s i.
Proof. rewrite alias_9_shape. apply output_418_reference. Qed.
Lemma output_480_reference s i ghost : to_Zpos (word_480 (encoded_leaves s i ghost)) = Reference.v445 s i.
Proof.
 rewrite scalar_integer_480 output_9_reference leaf_476_integer.
 unfold Reference.v445, Radix2Divider.CIRCTBits.word.
 change ((if Z.eqb (Reference.v412 s i) (normalize 64 (Reference.r14_npreviousOutput s)) then 1 else 0) =
  (if Z.eqb (Reference.v412 s i) (normalize 64 (Reference.r14_npreviousOutput s)) then 1 else 0) mod 2).
 destruct (Z.eqb (Reference.v412 s i) (normalize 64 (Reference.r14_npreviousOutput s))); reflexivity.
Qed.
Print Assumptions output_480_reference.
