From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import StatementFacts GroundFrames ConnectionFacts InstanceFoldFacts HierarchyFacts.
From SmallMultiplier Require Import InstanceChecks.
Lemma pass_scalar_connection invalid old before after stmts target source ground initial value bits
 (certificate:framed_write_certificate target (Sfcnct(Eid target)(Eref(Eid source))) stmts)
 (not_register:registers_frame target stmts=true)
 (different:source != target)
 (typed:type_of_val initial=Gtyp ground)
 (initial_found:VM.find target before=Some initial)
 (source_value:VM.find source old=Some value)
 (adapted:adapt_hvalue_as_type value (Gtyp ground)=Some(Gval ground bits))
 (ran:value_iter_with_memory_policy invalid empty_memory_map old false before stmts=Some after) :
 VM.find target after=Some(Gval ground bits).
Proof.
 eapply pass_framed_write_value; [exact certificate|exact not_register|exact typed|exact initial_found| |exact ran].
 intros position local_before local_after found step.
 eapply bidirectional_eid_target with (old:=old) (before:=local_before) (after:=local_after) (source:=source) (value:=value); [exact different| | |exact adapted|].
 - cbn [eval_type_of_ref]. rewrite found. cbn. rewrite typed. reflexivity.
 - cbn [eval_href_with_memory]. exact source_value.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Lemma pass_scalar_connection_type invalid old before after stmts target source ground initial
 (certificate:framed_write_certificate target (Sfcnct(Eid target)(Eref(Eid source))) stmts)
 (not_register:registers_frame target stmts=true)
 (different:source != target)
 (typed:type_of_val initial=Gtyp ground)
 (initial_found:VM.find target before=Some initial)
 (ran:value_iter_with_memory_policy invalid empty_memory_map old false before stmts=Some after) :
 exists result, VM.find target after=Some result /\ type_of_val result=Gtyp ground.
Proof.
 eapply pass_framed_write_ground_type; [exact certificate|exact not_register|exact typed|exact initial_found| |exact ran].
 intros position local_before local_after value found value_type step.
 eapply bidirectional_eid_preserves_target_type with (old:=old) (before:=local_before) (after:=local_after) (source:=source); [exact different| |].
 - cbn [eval_type_of_ref]. rewrite found. cbn. rewrite value_type. reflexivity.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Lemma circuit_pass_scalar_value invalid modules top snapshot final instances path module_id ports stmts target source ground value bits initial
 (instances_found:find_circuit_instances modules top=Some instances)
 (module_found:SVM.find path instances=Some module_id)
 (body_found:find_module modules module_id=Some(FInmod module_id ports stmts))
 (memory_empty:memory_map_for_module modules module_id=Some empty_memory_map)
 (certificate:framed_write_certificate target (Sfcnct(Eid target)(Eref(Eid source))) stmts)
 (not_register:registers_frame target stmts=true)
 (different:source != target)
 (initial_found:circuit_lookup path target snapshot=Some initial)
 (typed:type_of_val initial=Gtyp ground)
 (source_found:circuit_lookup path source snapshot=Some value)
 (adapted:adapt_hvalue_as_type value (Gtyp ground)=Some(Gval ground bits))
 (sync_frames:node_sync_check modules instances path target=true)
 (ran:circuit_value_iter_with_memory_policy invalid modules top snapshot false=Some final) :
 circuit_lookup path target final=Some(Gval ground bits).
Proof.
 destruct (circuit_iteration_local_steps _ _ _ _ _ _ ran) as [actual [evaluated [Found [Synced Steps]]]].
 rewrite instances_found in Found. inversion Found;subst actual.
 destruct (Steps path module_id module_found) as [before [after [Before [Step After]]]].
 unfold local_instance_update in Step. rewrite Before body_found memory_empty in Step.
 have Local:VM.find target after=Some(Gval ground bits).
 { eapply pass_scalar_connection; [exact certificate|exact not_register|exact different|exact typed| | |exact adapted|exact Step].
   - unfold circuit_lookup in initial_found. rewrite Before in initial_found. exact initial_found.
   - unfold circuit_lookup in source_found. rewrite Before in source_found. exact source_found. }
 rewrite (sync_circuit_preserves_lookup _ _ _ _ _ _ (node_sync_check_child _ _ _ _ sync_frames) (node_sync_check_parent _ _ _ _ sync_frames) Synced).
 unfold circuit_lookup. rewrite After. exact Local.
Qed.
Lemma circuit_pass_scalar_type invalid modules top snapshot final instances path module_id ports stmts target source ground initial
 (instances_found:find_circuit_instances modules top=Some instances)
 (module_found:SVM.find path instances=Some module_id)
 (body_found:find_module modules module_id=Some(FInmod module_id ports stmts))
 (memory_empty:memory_map_for_module modules module_id=Some empty_memory_map)
 (certificate:framed_write_certificate target (Sfcnct(Eid target)(Eref(Eid source))) stmts)
 (not_register:registers_frame target stmts=true)
 (different:source != target)
 (initial_found:circuit_lookup path target snapshot=Some initial)
 (typed:type_of_val initial=Gtyp ground)
 (sync_frames:node_sync_check modules instances path target=true)
 (ran:circuit_value_iter_with_memory_policy invalid modules top snapshot false=Some final) :
 exists result,circuit_lookup path target final=Some result /\ type_of_val result=Gtyp ground.
Proof.
 destruct (circuit_iteration_local_steps _ _ _ _ _ _ ran) as [actual [evaluated [Found [Synced Steps]]]].
 rewrite instances_found in Found. inversion Found;subst actual.
 destruct (Steps path module_id module_found) as [before [after [Before [Step After]]]].
 unfold local_instance_update in Step. rewrite Before body_found memory_empty in Step.
 have Local:exists result,VM.find target after=Some result /\ type_of_val result=Gtyp ground.
 { eapply pass_scalar_connection_type; [exact certificate|exact not_register|exact different|exact typed| |exact Step].
   unfold circuit_lookup in initial_found. rewrite Before in initial_found. exact initial_found. }
 destruct Local as [result [Result Typed]]. exists result;split;[|exact Typed].
 rewrite (sync_circuit_preserves_lookup _ _ _ _ _ _ (node_sync_check_child _ _ _ _ sync_frames) (node_sync_check_parent _ _ _ _ sync_frames) Synced).
 unfold circuit_lookup. rewrite After. exact Result.
Qed.
Print Assumptions circuit_pass_scalar_type.
