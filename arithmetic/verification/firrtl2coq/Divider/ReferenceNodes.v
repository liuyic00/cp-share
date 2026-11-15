From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths
  HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths.
From ArithmeticCommon Require Import BitvectorFacts.
From Divider Require Import Stable Representation.
Local Open Scope Z_scope.

Lemma numeric_equality_unsigned a b :
 (to_N a == to_N b) = Z.eqb (to_Zpos a) (to_Zpos b).
Proof.
 rewrite !to_Zpos_N.
 change (N.eqb (to_N a) (to_N b) = Z.eqb (Z.of_N (to_N a)) (Z.of_N (to_N b))).
 destruct (N.eqb_spec (to_N a) (to_N b)) as [E|E].
 - rewrite E Z.eqb_refl. reflexivity.
 - symmetry. apply Z.eqb_neq. intro H. apply E. now apply N2Z.inj.
Qed.

Lemma is_zero_unsigned bits : is_zero bits = Z.eqb (to_Zpos bits) 0.
Proof.
 destruct (is_zero bits) eqn:zero.
 - symmetry. apply Z.eqb_eq. apply is_zero_to_Zpos. exact zero.
 - symmetry. apply Z.eqb_neq. intro E.
   pose proof (to_Zpos0 E) as allzero.
   rewrite allzero zeros_is_zero in zero. discriminate.
Qed.

Lemma unsigned_singleton bit : to_Zpos [::bit] = if bit then 1 else 0.
Proof. destruct bit; reflexivity. Qed.

Transparent word_14 word_13.
Lemma node14_reference s i ghost :
 to_Zpos (word_14 (encoded_leaves s i ghost)) = Reference.v1 s i.
Proof.
 unfold word_14, closed_14, expr_14, word_of_eval.
 cbn [eval_hfexpr eval_href].
 rewrite VM.Lemmas.find_add_eq; last reflexivity.
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground.
 unfold word_13, encoded_leaves.
 change (to_Zpos [:: to_N (encode 3 (Reference.r0_nstate s)) == to_N [::false; false; false]] = Reference.v1 s i).
 rewrite numeric_equality_unsigned decode_encode.
 unfold Reference.v1, Reference.v0, Radix2Divider.CIRCTBits.word.
 change (to_Zpos [:: Z.eqb (normalize 3 (Reference.r0_nstate s)) 0] =
 ((if Z.eqb (Reference.r0_nstate s mod 8) 0 then 1 else 0) mod 2)).
 change (to_Zpos [:: Z.eqb (Reference.r0_nstate s mod 8) 0] =
 ((if Z.eqb (Reference.r0_nstate s mod 8) 0 then 1 else 0) mod 2)).
 destruct (Z.eqb (Reference.r0_nstate s mod 8) 0); reflexivity.
Qed.
Opaque word_14 word_13.
Print Assumptions node14_reference.
