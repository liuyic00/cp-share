From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths.
From ArithmeticCommon Require Import BitvectorFacts.
From Divider Require Import Stable Representation ReferenceNodes Slices Typing.
Local Open Scope Z_scope.
Lemma is_zero_onebit bits (sized : size bits = 1%nat) :
 is_zero bits = negb (Z.eqb (to_Zpos bits) 1).
Proof.
 destruct bits as [|bit bits]; first discriminate.
 destruct bits; last discriminate.
 destruct bit; reflexivity.
Qed.
Transparent word_68.
Lemma mux_68_shape v : word_68 v =
 if is_zero (word_66 v) then zext_to 2 (take 2 (word_67 v)) else [::false;true].
Proof.
 unfold word_68, closed_68, expr_68, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_66 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque word_68.
Lemma mux_68_reference s i ghost :
 to_Zpos (word_68 (encoded_leaves s i ghost)) = Reference.v81 s i.
Proof.
 rewrite mux_68_shape (is_zero_onebit _ (encoded_word_66_size s i ghost)) slice_66_reference.
 unfold Reference.v81, Reference.v78, Reference.v80, Reference.v26, Radix2Divider.CIRCTBits.word.
 destruct (Z.eqb (Reference.v77 s i) 1) eqn:guard; first reflexivity.
 cbn [negb]. unfold zext_to. rewrite unsigned_zero_extend unsigned_take -(slice_67_reference s i ghost).
 change ((to_Zpos (word_67 (encoded_leaves s i ghost)) mod 4) =
  ((to_Zpos (word_67 (encoded_leaves s i ghost)) mod 4) mod 4)).
 rewrite Z.mod_mod; [reflexivity|lia].
Qed.
Print Assumptions mux_68_reference.
