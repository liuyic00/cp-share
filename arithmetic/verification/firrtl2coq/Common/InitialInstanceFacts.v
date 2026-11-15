From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import StatementFacts InitialMapFacts.
Inductive initial_instance_certificate watched module_id : @hfstmt_seq VarOrder.T -> Prop :=
| initial_instance_here : forall rest,
 initial_sequence_frames watched rest=true -> initial_instance_certificate watched module_id (Qcons(Sinst watched module_id)rest)
| initial_instance_later : forall stmt rest,
 flat_statement stmt=true -> initial_instance_certificate watched module_id rest -> initial_instance_certificate watched module_id (Qcons stmt rest).
Lemma initial_instance_value modules previous watched module_id typ stmts
 (module_type_found:module_type modules module_id=Some typ)
 (certificate:initial_instance_certificate watched module_id stmts) :
 forall before after,statements_initial_map_with_memory modules stmts previous before=Some after -> VM.find watched after=Some(Needtobedefined typ).
Proof.
 induction certificate as [rest frames|stmt rest flat cert IH]; intros before after ran.
 - cbn [statements_initial_map_with_memory] in ran. rewrite module_type_found in ran.
   rewrite (initial_sequence_preserves _ _ _ _ _ _ frames ran). apply VM.Lemmas.find_add_eq. reflexivity.
 - rewrite (initial_flat_decompose _ _ _ _ _ flat) in ran.
   destruct (initial_one modules previous before stmt) as [middle|] eqn:One; [|discriminate].
   eapply IH; exact ran.
Qed.
Fixpoint checked_initial_instance watched module_id (stmts:@hfstmt_seq VarOrder.T) : bool :=
 match stmts with Qnil=>false
 | Qcons(Sinst id mi)rest=>if watched==id then (mi==module_id)&&initial_sequence_frames watched rest else checked_initial_instance watched module_id rest
 | Qcons stmt rest=>flat_statement stmt&&checked_initial_instance watched module_id rest end.
Lemma checked_initial_instance_sound watched module_id stmts :
 checked_initial_instance watched module_id stmts=true -> initial_instance_certificate watched module_id stmts.
Proof.
 induction stmts as [|stmt rest IH]; [discriminate|].
 destruct stmt as [|id typ|id reg|id mem|id mi|id expr|lhs expr|ref|cond yes no]; cbn [checked_initial_instance];
 try (move/andP=>[flat checked];apply initial_instance_later;[exact flat|exact(IH checked)]).
 destruct (watched==id) eqn:Same.
 - move/eqP:Same=>Same. subst id. move/andP=>[/eqP Same frames]. subst mi. apply initial_instance_here. exact frames.
 - intro checked. apply initial_instance_later;[reflexivity|exact(IH checked)].
Qed.
