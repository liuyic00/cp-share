From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ArithmeticCommon Require Import BitvectorFacts.
From Divider Require Import Stable Representation Typing ScalarOps Log2.
Local Open Scope Z_scope.
Lemma log2_208_reference s i ghost : to_Zpos (word_208 (encoded_leaves s i ghost)) = Reference.v226 s i.
Proof.
 pose proof (@to_Zpos_ge0 (word_207 (encoded_leaves s i ghost))) as lower.
 pose proof (@to_Zpos_bounded (word_207 (encoded_leaves s i ghost))) as upper.
 rewrite encoded_word_207_size in upper.
 rewrite log2_207_reference in lower upper.
 change (Reference.v224 s i < 64) in upper.
 rewrite scalar_integer_208 log2_207_reference.
 unfold Reference.v226, Reference.v225, Radix2Divider.CIRCTBits.word.
 change ((64 + Reference.v224 s i) mod 256 = (Reference.v224 s i + 64) mod 128).
 rewrite !Z.mod_small; lia.
Qed.
Print Assumptions log2_208_reference.
