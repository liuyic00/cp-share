From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths.
From ArithmeticCommon Require Import BitvectorFacts NormalizationFacts.
From Divider Require Import Stable Representation Typing SliceOps MuxShapes Concats LeafWords.
Local Open Scope Z_scope.
Local Opaque Reference.v407.
Section OutputSign.
Variables s : Reference.State.
Variable i : Reference.Inputs.
Variable ghost : Z.
Hypothesis value412 : to_Zpos (word_412 (encoded_leaves s i ghost)) = Reference.v407 s i.

Lemma output_slice_413_reference :
 to_Zpos (word_413 (encoded_leaves s i ghost)) = Reference.v410 s i.
Proof. rewrite slice_integer_413 value412. reflexivity. Qed.
Lemma output_slice_414_reference :
 to_Zpos (word_414 (encoded_leaves s i ghost)) = Reference.v408 s i.
Proof.
 rewrite slice_integer_414 slice_integer_413 Z.shiftr_0_r.
 rewrite (normalize_shiftr_nested 1 32 31); [|lia].
 rewrite value412. reflexivity.
Qed.
Lemma output_slice_415_reference :
 to_Zpos (word_415 (encoded_leaves s i ghost)) = Reference.v408 s i.
Proof.
 rewrite slice_integer_415 Z.shiftr_0_r output_slice_414_reference.
 change (normalize 1 (normalize 1 (Z.shiftr (Reference.v407 s i) 31)) = normalize 1 (Z.shiftr (Reference.v407 s i) 31)).
 apply normalize_nested. lia.
Qed.
Lemma output_sign_bit_cases : Reference.v408 s i = 0 \/ Reference.v408 s i = 1.
Proof.
 have Bound := normalize_range 1 (Z.shiftr (Reference.v407 s i) 31).
 change (0 <= Reference.v408 s i < 2) in Bound. lia.
Qed.
Lemma output_sign_416_reference :
 to_Zpos (word_416 (encoded_leaves s i ghost)) = Reference.v409 s i.
Proof.
 rewrite mux_integer_416 output_slice_415_reference.
 unfold Reference.v409.
 destruct output_sign_bit_cases as [Zero|One]; [rewrite Zero|rewrite One]; vm_compute; reflexivity.
Qed.
Local Opaque Reference.v409 Reference.v410.
Lemma output_concat_417_reference :
 to_Zpos (word_417 (encoded_leaves s i ghost)) = Reference.v411 s i.
Proof.
 have Raw := concat_integer_417 s i ghost.
 rewrite output_slice_413_reference output_sign_416_reference in Raw.
 unfold Reference.v411.
 rewrite Z.shiftl_mul_pow2; [|lia].
 change (to_Zpos (word_417 (encoded_leaves s i ghost)) = normalize 64 (Reference.v409 s i * modulus 32 + Reference.v410 s i)).
 rewrite Z.add_comm -Raw. symmetry. apply unsigned_normalized. apply encoded_word_417_size.
Qed.
Lemma output_mux_418_reference :
 to_Zpos (word_418 (encoded_leaves s i ghost)) = Reference.v412 s i.
Proof.
 rewrite mux_integer_418 leaf_46_integer output_concat_417_reference value412.
 reflexivity.
Qed.
End OutputSign.
Print Assumptions output_mux_418_reference.
