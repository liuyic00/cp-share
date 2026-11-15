From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import StatementFacts GroundFrames BundleFacts PortFieldFacts FieldStatementFacts FieldTypes FieldConnections.

Lemma repl_field_sink_passive instance field old value env result
 (passive : is_passive_value value = true)
 (replaced : repl_val_part (Esubfield (Eid instance) field) (replace_writeable Sink) old value env = Some result) :
 value_field field result = Some value.
Proof.
 change (match convert_to_bundle_value old with
 | Some bundle => option_map Bval (bundle_replace field (fun prior => replace_writeable Sink prior value) bundle)
 | None => None end = Some result) in replaced.
 unfold value_field. destruct (convert_to_bundle_value old) as [bundle|] eqn:B; try discriminate.
 destruct (bundle_replace field (fun prior => replace_writeable Sink prior value) bundle) as [next|] eqn:Next; inversion replaced; subst result.
 cbn [convert_to_bundle_value]. eapply bundle_replace_constant; [intros; apply replace_sink_passive; exact passive|exact Next].
Qed.

Lemma field_unidirectional_type mm old before after instance field rhs ground
 (target_type : eval_type_of_ref (Esubfield (Eid instance) field) before = Some (Gtyp ground))
 (ran : unidirectional_connect_bundle mm (Esubfield (Eid instance) field) rhs old before = Some after) :
 eval_type_of_ref (Esubfield (Eid instance) field) after = Some (Gtyp ground).
Proof.
 unfold unidirectional_connect_bundle in ran. cbn [HiF.base_ref] in ran.
 destruct (VM.find instance before) as [prior|] eqn:Found; try discriminate.
 rewrite target_type in ran.
 destruct (eval_hfexpr_with_memory mm rhs old old) as [value|]; try discriminate.
 destruct (adapt_hvalue_as_type value (Gtyp ground)) as [adapted|] eqn:Adapted; try discriminate.
 destruct (repl_val_part (Esubfield (Eid instance) field) (fun _ v => Some v) prior adapted old) as [result|] eqn:Updated; inversion ran; subst after.
 rewrite interface_field_type. unfold interface_field.
 rewrite VM.Lemmas.find_add_eq; [|reflexivity].
 rewrite (repl_field_direct_constant _ _ _ _ _ _ Updated).
 cbn [option_map]. rewrite (adapt_ground_type _ _ _ Adapted). reflexivity.
Qed.

Lemma field_bidirectional_type mm old before after instance field rhs ground
 (target_type : eval_type_of_ref (Esubfield (Eid instance) field) before = Some (Gtyp ground))
 (source_frames : field_ref_frames instance field rhs = true)
 (ran : bidirectional_connect_with_memory mm (Esubfield (Eid instance) field) rhs old before = Some after) :
 eval_type_of_ref (Esubfield (Eid instance) field) after = Some (Gtyp ground).
Proof.
 unfold bidirectional_connect_with_memory in ran. cbn [HiF.base_ref] in ran.
 destruct (VM.find instance before) as [prior|] eqn:Found; try discriminate.
 rewrite target_type in ran.
 destruct (eval_href_with_memory mm rhs old old) as [value|]; try discriminate.
 destruct (adapt_hvalue_as_type value (Gtyp ground)) as [adapted|] eqn:Adapted; try discriminate.
 destruct (repl_val_part (Esubfield (Eid instance) field) (replace_writeable Sink) prior adapted old) as [result|] eqn:Updated; try discriminate.
 cbn [option_map] in ran.
 have Written : interface_field instance field (VM.add instance result before) = Some adapted.
 { unfold interface_field. rewrite VM.Lemmas.find_add_eq; [|reflexivity].
   eapply repl_field_sink_passive; [eapply adapt_ground_passive; exact Adapted|exact Updated]. }
 destruct (VM.find (HiF.base_ref rhs) (VM.add instance result before)) as [prior2|] eqn:Found2; try discriminate.
 destruct (eval_type_of_ref rhs (VM.add instance result before)) as [ty2|]; try discriminate.
 destruct (eval_href_with_memory mm (Esubfield (Eid instance) field) old old) as [value2|]; try discriminate.
 destruct (adapt_hvalue_as_type value2 ty2) as [adapted2|]; try discriminate.
 destruct (repl_val_part rhs (replace_writeable Source) prior2 adapted2 old) as [result2|] eqn:Updated2; inversion ran; subst after.
 rewrite interface_field_type.
 rewrite (reference_update_preserves_field _ _ _ _ _ _ _ _ _ source_frames Found2 Updated2) Written.
 cbn [option_map]. rewrite (adapt_ground_type _ _ _ Adapted). reflexivity.
Qed.

Lemma one_statement_field_type invalid scope position old set_regs before after instance field rhs ground
 (target_type : eval_type_of_ref (Esubfield (Eid instance) field) before = Some (Gtyp ground))
 (source_frames : match rhs with Eref r => field_ref_frames instance field r | _ => true end = true)
 (ran : one_statement invalid scope position empty_memory_map old set_regs before
   (Sfcnct (Esubfield (Eid instance) field) rhs) = Some after) :
 eval_type_of_ref (Esubfield (Eid instance) field) after = Some (Gtyp ground).
Proof.
 destruct rhs; try (eapply one_statement_nonref in ran; [|reflexivity]);
 try (cbn [unidirectional_connect_with_memory] in ran;
   eapply field_unidirectional_type; [exact target_type|exact ran]).
 have flat : flat_ref (Esubfield (Eid instance) field) = true by reflexivity.
 have connection := one_statement_ref _ _ _ _ _ _ _ _ _ flat ran.
 eapply field_bidirectional_type; [exact target_type|exact source_frames|exact connection].
Qed.
Print Assumptions one_statement_field_type.

Lemma field_write_certificate_type invalid scope old set_regs instance field rhs ground stmts
 (certificate : field_write_certificate instance field (Sfcnct (Esubfield (Eid instance) field) rhs) stmts)
 (source_frames : match rhs with Eref r => field_ref_frames instance field r | _ => true end = true) :
 forall position before after,
 eval_type_of_ref (Esubfield (Eid instance) field) before = Some (Gtyp ground) ->
 value_iter_statements_with_memory_policy invalid scope position empty_memory_map old set_regs before stmts = Some after ->
 eval_type_of_ref (Esubfield (Eid instance) field) after = Some (Gtyp ground).
Proof.
 remember (Sfcnct (Esubfield (Eid instance) field) rhs) as writer eqn:Writer in certificate.
 induction certificate as [rest flat framed|stmt rest framed certificate IH]; intros position before after Initial ran.
 - subst writer. rewrite (flat_statement_decompose _ _ _ _ _ _ _ _ _ flat) in ran.
   destruct (one_statement invalid scope position empty_memory_map old set_regs before
     (Sfcnct (Esubfield (Eid instance) field) rhs)) as [middle|] eqn:Head; try discriminate.
   have Typed := one_statement_field_type _ _ _ _ _ _ _ _ _ _ _ Initial source_frames Head.
   rewrite interface_field_type in Typed. rewrite interface_field_type.
   rewrite (field_sequence_preserves _ _ _ _ _ _ _ _ _ _ framed ran). exact Typed.
 - rewrite (flat_statement_decompose _ _ _ _ _ _ _ _ _ (field_statement_flat _ _ _ framed)) in ran.
   destruct (one_statement invalid scope position empty_memory_map old set_regs before stmt) as [middle|] eqn:Head; try discriminate.
   eapply IH; [|exact ran].
   rewrite interface_field_type in Initial. rewrite interface_field_type.
   rewrite (one_statement_field_frame _ _ _ _ _ _ _ _ _ _ framed Head). exact Initial.
Qed.

Lemma pass_field_connect_type invalid old before after stmts instance field rhs ground
 (certificate : field_write_certificate instance field (Sfcnct (Esubfield (Eid instance) field) rhs) stmts)
 (not_register : registers_frame instance stmts = true)
 (initial_type : eval_type_of_ref (Esubfield (Eid instance) field) before = Some (Gtyp ground))
 (source_frames : match rhs with Eref r => field_ref_frames instance field r | _ => true end = true)
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before stmts = Some after) :
 eval_type_of_ref (Esubfield (Eid instance) field) after = Some (Gtyp ground).
Proof.
 unfold value_iter_with_memory_policy in ran.
 destruct (value_iter_statements_with_memory_policy invalid [::] 0 empty_memory_map old false before stmts) as [proposed|] eqn:Statements; try discriminate.
 rewrite interface_field_type. unfold interface_field.
 rewrite (finish_registers_preserves_other _ _ _ _ _ _ _ not_register ran).
 rewrite -interface_field_type.
 eapply field_write_certificate_type; [exact certificate|exact source_frames|exact initial_type|exact Statements].
Qed.
Print Assumptions pass_field_connect_type.
