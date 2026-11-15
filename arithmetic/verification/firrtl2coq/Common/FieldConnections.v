From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import StatementFacts BundleFacts PortFieldFacts FieldStatementFacts FieldTypes.

Lemma repl_field_direct_constant instance field old value env result
 (replaced : repl_val_part (Esubfield (Eid instance) field) (fun _ v => Some v) old value env = Some result) :
 value_field field result = Some value.
Proof.
 change (match convert_to_bundle_value old with
 | Some bundle => option_map Bval (bundle_replace field (fun _ => Some value) bundle)
 | None => None end = Some result) in replaced.
 unfold value_field. destruct (convert_to_bundle_value old) as [bundle|] eqn:B; try discriminate.
 destruct (bundle_replace field (fun _ => Some value) bundle) as [next|] eqn:Next; inversion replaced; subst result.
 cbn [convert_to_bundle_value]. eapply bundle_replace_constant; [intros; reflexivity|exact Next].
Qed.

Lemma field_unidirectional_value mm old before after instance field rhs ground value bits
 (target_type : eval_type_of_ref (Esubfield (Eid instance) field) before = Some (Gtyp ground))
 (evaluated : eval_hfexpr_with_memory mm rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : unidirectional_connect_bundle mm (Esubfield (Eid instance) field) rhs old before = Some after) :
 interface_field instance field after = Some (Gval ground bits).
Proof.
 unfold unidirectional_connect_bundle in ran. cbn [HiF.base_ref] in ran.
 destruct (VM.find instance before) as [prior|] eqn:Found; try discriminate.
 rewrite target_type evaluated adapted in ran.
 destruct (repl_val_part (Esubfield (Eid instance) field) (fun _ v => Some v) prior (Gval ground bits) old) as [result|] eqn:Updated; inversion ran; subst after.
 unfold interface_field. rewrite VM.Lemmas.find_add_eq; [|reflexivity].
 eapply repl_field_direct_constant. exact Updated.
Qed.

Lemma field_bidirectional_value mm old before after instance field rhs ground value bits
 (target_type : eval_type_of_ref (Esubfield (Eid instance) field) before = Some (Gtyp ground))
 (evaluated : eval_href_with_memory mm rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (source_frames : field_ref_frames instance field rhs = true)
 (ran : bidirectional_connect_with_memory mm (Esubfield (Eid instance) field) rhs old before = Some after) :
 interface_field instance field after = Some (Gval ground bits).
Proof.
 unfold bidirectional_connect_with_memory in ran. cbn [HiF.base_ref] in ran.
 destruct (VM.find instance before) as [prior|] eqn:Found; try discriminate.
 rewrite target_type evaluated adapted in ran.
 destruct (repl_val_part (Esubfield (Eid instance) field) (replace_writeable Sink) prior (Gval ground bits) old) as [result|] eqn:Updated; try discriminate.
 cbn [option_map] in ran.
 have Written : interface_field instance field (VM.add instance result before) = Some (Gval ground bits).
 { unfold interface_field. rewrite VM.Lemmas.find_add_eq; [|reflexivity]. eapply repl_field_sink_constant. exact Updated. }
 destruct (VM.find (HiF.base_ref rhs) (VM.add instance result before)) as [prior2|] eqn:Found2; try discriminate.
 destruct (eval_type_of_ref rhs (VM.add instance result before)) as [ty2|]; try discriminate.
 destruct (eval_href_with_memory mm (Esubfield (Eid instance) field) old old) as [value2|]; try discriminate.
 destruct (adapt_hvalue_as_type value2 ty2) as [adapted2|]; try discriminate.
 destruct (repl_val_part rhs (replace_writeable Source) prior2 adapted2 old) as [result2|] eqn:Updated2; inversion ran; subst after.
 rewrite -Written. eapply reference_update_preserves_field; [exact source_frames|exact Found2|exact Updated2].
Qed.

Lemma one_statement_field_value invalid scope position old set_regs before after instance field rhs ground value bits
 (target_type : eval_type_of_ref (Esubfield (Eid instance) field) before = Some (Gtyp ground))
 (evaluated : eval_hfexpr_with_memory empty_memory_map rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (source_frames : match rhs with Eref r => field_ref_frames instance field r | _ => true end = true)
 (ran : one_statement invalid scope position empty_memory_map old set_regs before
   (Sfcnct (Esubfield (Eid instance) field) rhs) = Some after) :
 interface_field instance field after = Some (Gval ground bits).
Proof.
 destruct rhs; try (eapply one_statement_nonref in ran; [|reflexivity]);
 try (cbn [unidirectional_connect_with_memory] in ran;
   eapply field_unidirectional_value; [exact target_type|exact evaluated|exact adapted|exact ran]).
 have flat : flat_ref (Esubfield (Eid instance) field) = true by reflexivity.
 have connection := one_statement_ref _ _ _ _ _ _ _ _ _ flat ran.
 eapply field_bidirectional_value; [exact target_type|exact evaluated|exact adapted|exact source_frames|exact connection].
Qed.
Print Assumptions one_statement_field_value.

Lemma pass_field_connect_value invalid old before after stmts instance field rhs ground value bits initial
 (certificate : field_write_certificate instance field (Sfcnct (Esubfield (Eid instance) field) rhs) stmts)
 (not_register : registers_frame instance stmts = true)
 (initial_field : interface_field instance field before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (source_frames : match rhs with Eref r => field_ref_frames instance field r | _ => true end = true)
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before stmts = Some after) :
 interface_field instance field after = Some (Gval ground bits).
Proof.
 eapply pass_field_write_value; [exact certificate|exact not_register|exact initial_field| |exact ran].
 intros position local_before local_after Initial Step.
 eapply one_statement_field_value; [|exact evaluated|exact adapted|exact source_frames|exact Step].
 rewrite interface_field_type Initial. cbn [option_map]. rewrite initial_type. reflexivity.
Qed.
Print Assumptions pass_field_connect_value.
