From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import HiFirrtl_with_implicit_widths.
From ArithmeticCommon Require Import StatementFacts GroundFrames.
Fixpoint checked_scalar_write watched (stmts:@hfstmt_seq VarOrder.T) : option (@hfstmt VarOrder.T) :=
 match stmts with
 | Qnil => None
 | Qcons stmt rest => if flat_statement_frames watched stmt then checked_scalar_write watched rest
   else if flat_statement stmt && flat_sequence_frames watched rest then Some stmt else None
 end.
Lemma checked_scalar_write_sound watched stmts : forall writer,
 checked_scalar_write watched stmts = Some writer -> framed_write_certificate watched writer stmts.
Proof.
 induction stmts as [|stmt rest IH]; intros writer H; [discriminate|].
 cbn [checked_scalar_write] in H.
 destruct (flat_statement_frames watched stmt) eqn:F.
 - apply framed_write_later; [exact F|apply IH;exact H].
 - destruct (flat_statement stmt && flat_sequence_frames watched rest) eqn:E; [|discriminate].
   move/andP:E=>[A B]. inversion H;subst. apply framed_write_here;assumption.
Qed.
