From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
  HiFirrtl_with_implicit_widths Semantics_with_implicit_widths.

(* The type-correctness invariant required by the original evaluator's theorem.
   This is not the stronger known-hardware-input domain predicate: values may
   contain interpreter markers if those markers carry their correct types. *)
Definition env_typed (env : VM.t hvalue) : Prop :=
  forall id value, VM.find id env = Some value ->
    hvalue_is_type_correct value (type_of_val value) = true.

Lemma env_typed_empty : env_typed (VM.empty hvalue).
Proof.
  intros id value found. rewrite VM.Lemmas.empty_o in found. discriminate.
Qed.

Lemma env_typed_add env id value
  (typed : env_typed env)
  (correct : hvalue_is_type_correct value (type_of_val value) = true) :
  env_typed (VM.add id value env).
Proof.
  intros key actual found. destruct (key == id) eqn:equal.
  - rewrite (VM.Lemmas.find_add_eq equal) in found.
    inversion found; subst actual; exact correct.
  - rewrite (VM.Lemmas.find_add_neq (elimF idP equal)) in found.
    exact (typed key actual found).
Qed.

Lemma env_typed_add_uint env id width bits
  (typed : env_typed env) (bounded : size bits = width) :
  env_typed (VM.add id (Gval (Fuint width) bits) env).
Proof.
  apply env_typed_add; [exact typed|].
  cbn [hvalue_is_type_correct type_of_val]. rewrite bounded !eq_refl. reflexivity.
Qed.

Lemma env_typed_add_clock env id bits
  (typed : env_typed env) (bounded : size bits = 1%nat) :
  env_typed (VM.add id (Gval Fclock bits) env).
Proof.
  apply env_typed_add; [exact typed|].
  cbn [hvalue_is_type_correct type_of_val]. rewrite bounded. reflexivity.
Qed.

Lemma env_typed_evaluator_condition env (typed : env_typed env) id :
  match VM.find id env with
  | Some value => hvalue_is_type_correct value (type_of_val value)
  | None => true
  end.
Proof.
  destruct (VM.find id env) as [value|] eqn:found;
    [exact (typed id value found)|reflexivity].
Qed.

(* The upstream eval_hfexpr_type_correct is Admitted. Do not use it to
   manufacture a type-preservation certificate for a hardware proof. *)
Lemma uint_value_typed_size actual_width expected_width bits
  (correct : hvalue_is_type_correct (Gval (Fuint actual_width) bits)
    (Gtyp (Fuint expected_width)) = true) : size bits = expected_width.
Proof.
  cbn [hvalue_is_type_correct] in correct.
  move/andP: correct => [/eqP bounded /eqP same_width].
  rewrite bounded same_width. reflexivity.
Qed.

Lemma env_typed_lookup_uint_size env id width bits
  (typed : env_typed env) (found : VM.find id env = Some (Gval (Fuint width) bits)) :
  size bits = width.
Proof.
  apply (uint_value_typed_size width width bits).
  exact (typed id _ found).
Qed.

Print Assumptions env_typed_add_uint.
Print Assumptions env_typed_lookup_uint_size.
