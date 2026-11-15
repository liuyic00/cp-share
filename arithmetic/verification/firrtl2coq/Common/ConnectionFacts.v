From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import StatementFacts.

Lemma bidirectional_eid_target mm old before after target source ground value bits
 (different : source != target)
 (target_type : eval_type_of_ref (@Eid VarOrder.T target) before = Some (Gtyp ground))
 (source_value : eval_href_with_memory mm (@Eid VarOrder.T source) old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : bidirectional_connect_with_memory mm (@Eid VarOrder.T target) (@Eid VarOrder.T source) old before = Some after) :
 VM.find target after = Some (Gval ground bits).
Proof.
 unfold bidirectional_connect_with_memory in ran.
 cbn [HiF.base_ref] in ran.
 destruct (VM.find target before) as [previous|] eqn:Previous; try discriminate.
 rewrite target_type source_value adapted in ran.
 cbn [repl_val_part replace_writeable is_passive_value option_map] in ran.
 repeat match type of ran with
 | context [match ?x with Some _ => _ | None => _ end] => destruct x eqn:?
 | context [option_map ?f ?x] => destruct x eqn:?; cbn [option_map] in ran
 end; try discriminate.
 inversion ran; subst.
 rewrite (find_add_other _ _ _ _ different).
 apply VM.Lemmas.find_add_eq. exact (eq_refl target).
Qed.

Inductive write_certificate (watched : VarOrder.T) (writer : @hfstmt VarOrder.T) :
 @hfstmt_seq VarOrder.T -> Prop :=
| write_certificate_here : forall rest,
 flat_statement writer = true -> flat_sequence_frames watched rest = true ->
 write_certificate watched writer (Qcons writer rest)
| write_certificate_later : forall stmt rest,
 flat_statement stmt = true -> write_certificate watched writer rest ->
 write_certificate watched writer (Qcons stmt rest).

Lemma write_certificate_value invalid scope old set_regs watched writer ground bits stmts
 (certificate : write_certificate watched writer stmts)
 (writes : forall position before after,
   one_statement invalid scope position empty_memory_map old set_regs before writer = Some after ->
   VM.find watched after = Some (Gval ground bits)) :
 forall position before after,
 value_iter_statements_with_memory_policy invalid scope position empty_memory_map old set_regs before stmts = Some after ->
 VM.find watched after = Some (Gval ground bits).
Proof.
 induction certificate as [rest flat framed|stmt rest flat certificate IH]; intros position before after ran.
 - rewrite (flat_statement_decompose _ _ _ _ _ _ _ _ _ flat) in ran.
   destruct (one_statement invalid scope position empty_memory_map old set_regs before writer) as [middle|] eqn:Head; try discriminate.
   eapply flat_sequence_preserves_known; [exact framed|eapply writes; exact Head|exact ran].
 - rewrite (flat_statement_decompose _ _ _ _ _ _ _ _ _ flat) in ran.
   destruct (one_statement invalid scope position empty_memory_map old set_regs before stmt) as [middle|] eqn:Head; try discriminate.
   eapply IH. exact ran.
Qed.

Lemma pass_write_value invalid old before after stmts watched writer ground bits
 (certificate : write_certificate watched writer stmts)
 (not_register : registers_frame watched stmts = true)
 (writes : forall position initial final,
   one_statement invalid [::] position empty_memory_map old false initial writer = Some final ->
   VM.find watched final = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before stmts = Some after) :
 VM.find watched after = Some (Gval ground bits).
Proof.
 unfold value_iter_with_memory_policy in ran.
 destruct (value_iter_statements_with_memory_policy invalid [::] 0 empty_memory_map old false before stmts) as [proposed|] eqn:Statements; try discriminate.
 rewrite (finish_registers_preserves_other _ _ _ _ _ _ _ not_register ran).
 eapply write_certificate_value; eassumption.
Qed.
Print Assumptions pass_write_value.
