From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From ArithmeticCommon Require Import BitvectorFacts.
From Divider Require Import Stable Representation Typing ReferenceNodes ScalarOps LeafWords.
Local Open Scope Z_scope.
Transparent word_14 word_420.
Lemma ready_same_state_test v : word_420 v = word_14 v.
Proof. reflexivity. Qed.
Opaque word_14 word_420.
Lemma control_420_reference s i ghost : to_Zpos (word_420 (encoded_leaves s i ghost)) = Reference.v1 s i.
Proof. rewrite ready_same_state_test. apply node14_reference. Qed.
Lemma control_2_reference s i ghost : to_Zpos (word_2 (encoded_leaves s i ghost)) = Reference.v1 s i.
Proof. rewrite alias_2_shape. apply control_420_reference. Qed.
Lemma control_15_reference s i ghost : to_Zpos (word_15 (encoded_leaves s i ghost)) = Reference.v2 s i.
Proof.
 transitivity (normalize 1 (to_Zpos (word_15 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_15_size.
 - rewrite scalar_integer_15 control_2_reference leaf_3_integer.
   unfold Reference.v2, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity.
Qed.
Lemma onebit_and_absorb a b (sa : size a = 1%nat) (sb : size b = 1%nat) : andB a (andB a b) = andB a b.
Proof.
 destruct a as [|a aa]; first discriminate. destruct aa; last discriminate.
 destruct b as [|b bb]; first discriminate. destruct bb; last discriminate.
 destruct a, b; reflexivity.
Qed.
Lemma control_16_reference s i ghost : to_Zpos (word_16 (encoded_leaves s i ghost)) = Reference.v2 s i.
Proof.
 rewrite scalar_shape_16 scalar_shape_15 alias_2_shape ready_same_state_test.
 rewrite onebit_and_absorb; [|apply encoded_word_14_size|apply encoded_word_3_size].
 rewrite -(ready_same_state_test (encoded_leaves s i ghost)) -alias_2_shape -scalar_shape_15.
 apply control_15_reference.
Qed.
Print Assumptions control_16_reference.
