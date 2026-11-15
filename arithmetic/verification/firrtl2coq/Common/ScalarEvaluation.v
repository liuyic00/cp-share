From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
  HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.

(* A syntactic certificate for the scalar fragment. In particular, a reference
   is a plain identifier: memory-reader fields, arrays and dynamic indices are
   excluded, rather than being silently interpreted as scalar references. *)
Fixpoint scalar_exprb (e : @hfexpr VarOrder.T) : bool :=
  match e with
  | Econst _ _ | Eref (Eid _) => true
  | Ecast _ body | Eprim_unop _ body => scalar_exprb body
  | Eprim_binop _ lhs rhs | Evalidif lhs rhs => scalar_exprb lhs && scalar_exprb rhs
  | Emux guard yes no => scalar_exprb guard && scalar_exprb yes && scalar_exprb no
  | Eref _ => false
  end.

(* This is independent of the memory layout: the certified fragment never
   consults it. It also covers pending/invalid guards, not just defined values. *)
Lemma scalar_eval_memory_irrelevant (mm : memory_map) (e : @hfexpr VarOrder.T)
  (old new : VM.t hvalue) (scalar : scalar_exprb e) :
  eval_hfexpr_with_memory mm e old new = eval_hfexpr e old new.
Proof.
  revert old new scalar.
  induction e as [typ bits|cast body IH|op body IH|op lhs IHleft rhs IHright|
    guard IHguard yes IHyes no IHno|guard IHguard body IHbody|reference];
    intros old new scalar.
  - reflexivity.
  - destruct cast; cbn [eval_hfexpr_with_memory eval_hfexpr]; rewrite (IH old new scalar); reflexivity.
  - cbn [eval_hfexpr_with_memory eval_hfexpr]; rewrite (IH old new scalar); reflexivity.
  - move/andP: scalar => [left_scalar right_scalar].
    cbn [eval_hfexpr_with_memory eval_hfexpr].
    rewrite (IHleft old new left_scalar) (IHright old new right_scalar). reflexivity.
  - move/andP: scalar => [/andP [guard_scalar yes_scalar] no_scalar].
    cbn [eval_hfexpr_with_memory eval_hfexpr].
    rewrite (IHguard old new guard_scalar) (IHyes old new yes_scalar) (IHno old new no_scalar).
    reflexivity.
  - move/andP: scalar => [guard_scalar body_scalar].
    cbn [eval_hfexpr_with_memory eval_hfexpr].
    rewrite (IHguard old new guard_scalar) (IHbody old new body_scalar). reflexivity.
  - destruct reference; try discriminate scalar. reflexivity.
Qed.

Corollary scalar_eval_empty_memory (e : @hfexpr VarOrder.T)
  (old new : VM.t hvalue) (scalar : scalar_exprb e) :
  eval_hfexpr_with_memory empty_memory_map e old new = eval_hfexpr e old new.
Proof. exact (scalar_eval_memory_irrelevant empty_memory_map e old new scalar). Qed.

Print Assumptions scalar_eval_memory_irrelevant.
