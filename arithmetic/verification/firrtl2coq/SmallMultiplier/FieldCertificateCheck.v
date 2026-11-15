From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import HiFirrtl_with_implicit_widths.
From ArithmeticCommon Require Import StatementFacts FieldStatementFacts.
Fixpoint checked_field_write instance field (stmts:@hfstmt_seq VarOrder.T) : option (@hfstmt VarOrder.T) :=
 match stmts with
 | Qnil => None
 | Qcons stmt rest => if field_statement_frames instance field stmt then checked_field_write instance field rest
   else if flat_statement stmt && field_sequence_frames instance field rest then Some stmt else None
 end.
Lemma checked_field_write_sound instance field stmts : forall writer,
 checked_field_write instance field stmts = Some writer -> field_write_certificate instance field writer stmts.
Proof.
 induction stmts as [|stmt rest IH]; intros writer H; [discriminate|].
 cbn [checked_field_write] in H.
 destruct (field_statement_frames instance field stmt) eqn:F.
 - apply field_write_later; [exact F|apply IH;exact H].
 - destruct (flat_statement stmt && field_sequence_frames instance field rest) eqn:E; [|discriminate].
   move/andP: E=>[A B]. inversion H;subst. apply field_write_here; assumption.
Qed.
