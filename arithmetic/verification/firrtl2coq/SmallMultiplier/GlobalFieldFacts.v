From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import StatementFacts HierarchyFacts FieldStatementFacts FieldConnections FieldTypes FieldTypePreservation InstanceFoldFacts PortFieldFacts SourceFieldFrames.
From SmallMultiplier Require Import InstanceChecks.
Lemma circuit_pass_field_value invalid modules top snapshot final instances path module_id ports stmts instance field rhs ground value bits initial
 (instances_found : find_circuit_instances modules top = Some instances)
 (module_found : SVM.find path instances = Some module_id)
 (body_found : find_module modules module_id = Some (FInmod module_id ports stmts))
 (memory_empty : memory_map_for_module modules module_id = Some empty_memory_map)
 (certificate : field_write_certificate instance field (Sfcnct (Esubfield (Eid instance) field) rhs) stmts)
 (not_register : registers_frame instance stmts = true)
 (initial_field : circuit_interface path instance field snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluates : forall old, SVM.find path snapshot = Some old -> eval_hfexpr_with_memory empty_memory_map rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (source_frames : match rhs with Eref r => field_ref_frames instance field r | _ => true end = true)
 (sync_frames : field_sync_check modules instances path instance field = true)
 (ran : circuit_value_iter_with_memory_policy invalid modules top snapshot false = Some final) :
 circuit_interface path instance field final = Some (Gval ground bits).
Proof.
 destruct (circuit_iteration_local_steps _ _ _ _ _ _ ran) as [actual [evaluated [Found [Synced Steps]]]].
 rewrite instances_found in Found. inversion Found; subst actual.
 destruct (Steps path module_id module_found) as [before [after [Before [Step After]]]].
 unfold local_instance_update in Step. rewrite Before body_found memory_empty in Step.
 have Local : interface_field instance field after = Some (Gval ground bits).
 { eapply pass_field_connect_value; [exact certificate|exact not_register| |exact initial_type|apply evaluates;exact Before|exact adapted|exact source_frames|exact Step].
   unfold circuit_interface, circuit_lookup in initial_field. rewrite Before in initial_field. exact initial_field. }
 rewrite (sync_circuit_preserves_interface _ _ _ _ _ _ _ (field_sync_check_child _ _ _ _ _ sync_frames) (field_sync_check_parent _ _ _ _ _ sync_frames) Synced).
 unfold circuit_interface, circuit_lookup. rewrite After. exact Local.
Qed.
Lemma circuit_pass_field_type invalid modules top snapshot final instances path module_id ports stmts instance field rhs ground
 (instances_found : find_circuit_instances modules top = Some instances)
 (module_found : SVM.find path instances = Some module_id)
 (body_found : find_module modules module_id = Some (FInmod module_id ports stmts))
 (memory_empty : memory_map_for_module modules module_id = Some empty_memory_map)
 (certificate : field_write_certificate instance field (Sfcnct (Esubfield (Eid instance) field) rhs) stmts)
 (not_register : registers_frame instance stmts = true)
 (initial_type : option_map type_of_val (circuit_interface path instance field snapshot) = Some (Gtyp ground))
 (source_frames : match rhs with Eref r => field_ref_frames instance field r | _ => true end = true)
 (sync_frames : field_sync_check modules instances path instance field = true)
 (ran : circuit_value_iter_with_memory_policy invalid modules top snapshot false = Some final) :
 option_map type_of_val (circuit_interface path instance field final) = Some (Gtyp ground).
Proof.
 destruct (circuit_iteration_local_steps _ _ _ _ _ _ ran) as [actual [evaluated [Found [Synced Steps]]]].
 rewrite instances_found in Found. inversion Found; subst actual.
 destruct (Steps path module_id module_found) as [before [after [Before [Step After]]]].
 unfold local_instance_update in Step. rewrite Before body_found memory_empty in Step.
 have Local : eval_type_of_ref (Esubfield (Eid instance) field) after = Some (Gtyp ground).
 { eapply pass_field_connect_type; [exact certificate|exact not_register| |exact source_frames|exact Step].
   rewrite interface_field_type. unfold circuit_interface, circuit_lookup in initial_type. rewrite Before in initial_type. exact initial_type. }
 rewrite (sync_circuit_preserves_interface _ _ _ _ _ _ _ (field_sync_check_child _ _ _ _ _ sync_frames) (field_sync_check_parent _ _ _ _ _ sync_frames) Synced).
 unfold circuit_interface, circuit_lookup. rewrite After.
 rewrite interface_field_type in Local. exact Local.
Qed.
Print Assumptions circuit_pass_field_type.
