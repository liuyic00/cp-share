From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import HiFirrtl_with_implicit_widths.
From ArithmeticCommon Require Import StatementFacts GroundFrames.
Fixpoint flat_register_check watched (stmts:@hfstmt_seq VarOrder.T) :=
 match stmts with
 | Qnil=>false
 | Qcons (Sreg id _) rest=>if id==watched then flat_register_sequence rest else flat_register_check watched rest
 | Qcons stmt rest=>flat_statement stmt && flat_register_check watched rest
 end.
Lemma flat_register_check_sound watched stmts :
 flat_register_check watched stmts=true -> flat_register_certificate watched stmts.
Proof.
 induction stmts as [|stmt rest IH]; intros H; [discriminate|].
 destruct stmt as [|id t|id reg|id mem|id mi|id expr|lhs rhs|r|c yes no]; cbn [flat_register_check flat_statement] in H;
 try (apply flat_register_later; [reflexivity|apply IH;exact H]); try discriminate.
 destruct(id==watched)eqn:E.
 - move/eqP:E=>E;subst id. apply flat_register_here. exact H.
 - apply flat_register_later;[reflexivity|apply IH;exact H].
Qed.
