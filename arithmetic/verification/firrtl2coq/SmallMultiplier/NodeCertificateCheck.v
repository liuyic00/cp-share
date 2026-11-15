From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import HiFirrtl_with_implicit_widths.
From ArithmeticCommon Require Import StatementFacts.
Fixpoint checked_node (watched : VarOrder.T) (stmts : @hfstmt_seq VarOrder.T) : option (@hfexpr VarOrder.T) :=
 match stmts with
 | Qnil => None
 | Qcons stmt rest =>
   match stmt with
   | Snode id expr => if id == watched then
       if flat_sequence_frames watched rest then Some expr else None
       else checked_node watched rest
   | _ => if flat_statement stmt then checked_node watched rest else None
   end
 end.
Lemma checked_node_sound watched stmts : forall expr,
 checked_node watched stmts = Some expr -> node_certificate watched expr stmts.
Proof.
 induction stmts as [|stmt rest IH]; intros expr H; [discriminate|].
 destruct stmt as [|id t|id reg|id mem|id mid|id rhs|lhs rhs|r|c yes no]; cbn [checked_node] in H;
 try (apply node_certificate_later; [reflexivity|apply IH; exact H]);
 try discriminate.
 destruct (id == watched) eqn:E.
 - move/eqP: E=>E; subst id.
   destruct (flat_sequence_frames watched rest) eqn:F; [|discriminate].
   inversion H; subst. apply node_certificate_here. exact F.
 - apply node_certificate_later; [reflexivity|apply IH; exact H].
Qed.
