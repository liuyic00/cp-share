From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import StatementFacts BundleFacts PortFieldFacts.

Definition field_ref_frames instance field (r : @href VarOrder.T) :=
 match r with
 | Eid id => id != instance
 | Esubfield (Eid id) fld => (id != instance) || (fld != field)
 | _ => false end.
Lemma framed_reference_flat instance field r
 (frame : field_ref_frames instance field r = true) : flat_ref r = true.
Proof. destruct r; try (destruct r); cbn [field_ref_frames] in frame; try discriminate; reflexivity. Qed.

Lemma reference_update_preserves_field instance field r fn new env before prior result
 (frame : field_ref_frames instance field r = true)
 (found : VM.find (HiF.base_ref r) before = Some prior)
 (updated : repl_val_part r fn prior new env = Some result) :
 interface_field instance field (VM.add (HiF.base_ref r) result before) = interface_field instance field before.
Proof.
 destruct r as [id|r fld|r idx|r expr]; cbn [field_ref_frames] in frame; try discriminate.
 - unfold interface_field. cbn [HiF.base_ref]. rewrite find_add_other; [reflexivity|exact frame].
 - destruct r as [id|r f|r i|r e]; try discriminate. cbn [HiF.base_ref] in *.
   destruct (id != instance) eqn:Different.
   + unfold interface_field. rewrite find_add_other; [reflexivity|exact Different].
   + have Same : id = instance by (move/negPn/eqP: Different => E; exact E).
     subst id. cbn in frame.
     unfold interface_field. rewrite VM.Lemmas.find_add_eq; [|reflexivity]. rewrite found.
     eapply repl_field_other; [exact (different_id _ _ frame)|exact updated].
Qed.

Lemma field_unidirectional_frame mm old before after lhs rhs instance field
 (frame : field_ref_frames instance field lhs = true)
 (ran : unidirectional_connect_bundle mm lhs rhs old before = Some after) :
 interface_field instance field after = interface_field instance field before.
Proof.
 unfold unidirectional_connect_bundle in ran.
 destruct (VM.find (HiF.base_ref lhs) before) as [prior|] eqn:Found; try discriminate.
 destruct (eval_type_of_ref lhs before); try discriminate.
 destruct (eval_hfexpr_with_memory mm rhs old old); try discriminate.
 destruct (adapt_hvalue_as_type h f); try discriminate.
 destruct (repl_val_part lhs (fun _ value => Some value) prior h0 old) as [result|] eqn:Updated; inversion ran; subst after.
 eapply reference_update_preserves_field; eassumption.
Qed.

Lemma field_bidirectional_frame mm old before after lhs rhs instance field
 (left_frame : field_ref_frames instance field lhs = true)
 (right_frame : field_ref_frames instance field rhs = true)
 (ran : bidirectional_connect_with_memory mm lhs rhs old before = Some after) :
 interface_field instance field after = interface_field instance field before.
Proof.
 unfold bidirectional_connect_with_memory in ran.
 destruct (VM.find (HiF.base_ref lhs) before) as [prior|] eqn:Found; try discriminate.
 destruct (eval_type_of_ref lhs before) as [ty|]; try discriminate.
 destruct (eval_href_with_memory mm rhs old old) as [value|]; try discriminate.
 destruct (adapt_hvalue_as_type value ty) as [adapted|]; try discriminate.
 destruct (repl_val_part lhs (replace_writeable Sink) prior adapted old) as [result|] eqn:Updated; try discriminate.
 cbn [option_map] in ran.
 have Kept : interface_field instance field (VM.add (HiF.base_ref lhs) result before) = interface_field instance field before.
 { eapply reference_update_preserves_field; eassumption. }
 destruct (VM.find (HiF.base_ref rhs) (VM.add (HiF.base_ref lhs) result before)) as [prior2|] eqn:Found2; try discriminate.
 destruct (eval_type_of_ref rhs (VM.add (HiF.base_ref lhs) result before)) as [ty2|]; try discriminate.
 destruct (eval_href_with_memory mm lhs old old) as [value2|]; try discriminate.
 destruct (adapt_hvalue_as_type value2 ty2) as [adapted2|]; try discriminate.
 destruct (repl_val_part rhs (replace_writeable Source) prior2 adapted2 old) as [result2|] eqn:Updated2; inversion ran; subst after.
 rewrite -Kept. eapply reference_update_preserves_field; eassumption.
Qed.

Definition field_statement_frames instance field (stmt : @hfstmt VarOrder.T) :=
 match stmt with
 | Sskip | Sinst _ _ => true
 | Swire id _ | Sreg id _ | Snode id _ => id != instance
 | Sfcnct lhs rhs => field_ref_frames instance field lhs &&
   match rhs with Eref r => field_ref_frames instance field r | _ => true end
 | _ => false end.
Fixpoint field_sequence_frames instance field (stmts : @hfstmt_seq VarOrder.T) :=
 match stmts with Qnil => true | Qcons stmt rest =>
 field_statement_frames instance field stmt && field_sequence_frames instance field rest end.
Lemma field_statement_flat instance field stmt
 (frame : field_statement_frames instance field stmt = true) : flat_statement stmt = true.
Proof. destruct stmt; try discriminate; reflexivity. Qed.

Lemma one_statement_field_frame invalid scope position old set_regs before after stmt instance field
 (frame : field_statement_frames instance field stmt = true)
 (ran : one_statement invalid scope position empty_memory_map old set_regs before stmt = Some after) :
 interface_field instance field after = interface_field instance field before.
Proof.
 destruct stmt as [|id t|id reg|id mem|id module_id|id expr|lhs expr|ref|cond yes no];
 cbn [field_statement_frames] in frame; try discriminate.
 - inversion ran; reflexivity.
 - inversion ran; subst. unfold interface_field. rewrite find_add_other; [reflexivity|exact frame].
 - cbn [one_statement value_iter_statements_with_memory_policy] in ran.
   destruct (VM.find id old); inversion ran; subst.
   unfold interface_field. rewrite find_add_other; [reflexivity|exact frame].
 - inversion ran; reflexivity.
 - cbn [one_statement value_iter_statements_with_memory_policy] in ran.
   destruct (eval_hfexpr_with_memory empty_memory_map expr old old); inversion ran; subst.
   unfold interface_field. rewrite find_add_other; [reflexivity|exact frame].
 - move/andP: frame => [left_frame right_frame].
   have flat := framed_reference_flat _ _ _ left_frame.
   destruct expr; try (eapply one_statement_nonref in ran; [|reflexivity]);
   try (rewrite (flat_ref_unidirectional _ _ _ _ _ _ flat) in ran;
     eapply field_unidirectional_frame; eassumption).
   have connection := one_statement_ref _ _ _ _ _ _ _ _ _ flat ran.
   eapply field_bidirectional_frame; [exact left_frame|exact right_frame|exact connection].
Qed.

Lemma field_sequence_preserves invalid scope old set_regs instance field stmts :
 forall position before after,
 field_sequence_frames instance field stmts = true ->
 value_iter_statements_with_memory_policy invalid scope position empty_memory_map old set_regs before stmts = Some after ->
 interface_field instance field after = interface_field instance field before.
Proof.
 induction stmts as [|stmt rest IH]; intros position before after frame ran.
 - inversion ran; reflexivity.
 - move/andP: frame => [head_frame tail_frame].
   rewrite (flat_statement_decompose _ _ _ _ _ _ _ _ _ (field_statement_flat _ _ _ head_frame)) in ran.
   destruct (one_statement invalid scope position empty_memory_map old set_regs before stmt) as [middle|] eqn:Head; try discriminate.
   rewrite (IH _ _ _ tail_frame ran). eapply one_statement_field_frame; eassumption.
Qed.

Inductive field_write_certificate instance field (writer : @hfstmt VarOrder.T) : @hfstmt_seq VarOrder.T -> Prop :=
| field_write_here : forall rest,
 flat_statement writer = true -> field_sequence_frames instance field rest = true ->
 field_write_certificate instance field writer (Qcons writer rest)
| field_write_later : forall stmt rest,
 field_statement_frames instance field stmt = true ->
 field_write_certificate instance field writer rest ->
 field_write_certificate instance field writer (Qcons stmt rest).

Lemma field_write_certificate_value invalid scope old set_regs instance field writer value initial stmts
 (certificate : field_write_certificate instance field writer stmts)
 (writes : forall position before after,
   interface_field instance field before = initial ->
   one_statement invalid scope position empty_memory_map old set_regs before writer = Some after ->
   interface_field instance field after = Some value) :
 forall position before after,
 interface_field instance field before = initial ->
 value_iter_statements_with_memory_policy invalid scope position empty_memory_map old set_regs before stmts = Some after ->
 interface_field instance field after = Some value.
Proof.
 induction certificate as [rest flat framed|stmt rest framed certificate IH]; intros position before after Initial ran.
 - rewrite (flat_statement_decompose _ _ _ _ _ _ _ _ _ flat) in ran.
   destruct (one_statement invalid scope position empty_memory_map old set_regs before writer) as [middle|] eqn:Head; try discriminate.
   rewrite (field_sequence_preserves _ _ _ _ _ _ _ _ _ _ framed ran). eapply writes; eassumption.
 - rewrite (flat_statement_decompose _ _ _ _ _ _ _ _ _ (field_statement_flat _ _ _ framed)) in ran.
   destruct (one_statement invalid scope position empty_memory_map old set_regs before stmt) as [middle|] eqn:Head; try discriminate.
   eapply IH; [|exact ran]. rewrite (one_statement_field_frame _ _ _ _ _ _ _ _ _ _ framed Head). exact Initial.
Qed.

Lemma pass_field_write_value invalid old before after stmts instance field writer value initial
 (certificate : field_write_certificate instance field writer stmts)
 (not_register : registers_frame instance stmts = true)
 (initial_field : interface_field instance field before = initial)
 (writes : forall position local_before local_after,
   interface_field instance field local_before = initial ->
   one_statement invalid [::] position empty_memory_map old false local_before writer = Some local_after ->
   interface_field instance field local_after = Some value)
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before stmts = Some after) :
 interface_field instance field after = Some value.
Proof.
 unfold value_iter_with_memory_policy in ran.
 destruct (value_iter_statements_with_memory_policy invalid [::] 0 empty_memory_map old false before stmts) as [proposed|] eqn:Statements; try discriminate.
 unfold interface_field.
 rewrite (finish_registers_preserves_other _ _ _ _ _ _ _ not_register ran).
 change (interface_field instance field proposed = Some value).
 eapply field_write_certificate_value; eassumption.
Qed.
Print Assumptions pass_field_write_value.
