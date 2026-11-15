From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import HierarchyFacts InstanceFoldFacts PortFieldFacts SourceFieldFrames CircuitPortTypes.
From SmallMultiplier Require Import InstanceChecks.
Lemma circuit_pass_input_link invalid modules top snapshot final instances instance parent module_id prefix suffix body input ground bits
 (instances_found:find_circuit_instances modules top=Some instances)
 (instance_found:SVM.find (instance::parent) instances=Some module_id)
 (module_found:find_module modules module_id=Some(FInmod module_id (prefix++Finput input (Gtyp ground)::suffix) body))
 (suffix_frames:all(child_port_frames input)suffix=true)
 (field_frames:field_sync_check modules instances parent instance input=true)
 (parent_frames:parent_only_check instances (instance::parent) input=true)
 (source_after:circuit_interface parent instance input final=Some(Gval ground bits))
 (ran:circuit_value_iter_with_memory_policy invalid modules top snapshot false=Some final) :
 circuit_lookup (instance::parent) input final=Some(Gval ground bits).
Proof.
 destruct (circuit_iteration_local_steps _ _ _ _ _ _ ran) as [actual [evaluated [Found [Synced Steps]]]].
 rewrite instances_found in Found. inversion Found;subst actual.
 rewrite (sync_circuit_preserves_interface _ _ _ _ _ _ _ (field_sync_check_child _ _ _ _ _ field_frames) (field_sync_check_parent _ _ _ _ _ field_frames) Synced) in source_after.
 eapply sync_circuit_child_input; [exact instance_found|exact module_found|exact suffix_frames| |exact(parent_only_check_sound _ _ _ parent_frames)|exact Synced].
 intros parent_env found. unfold circuit_interface,circuit_lookup in source_after. rewrite found in source_after.
 rewrite interface_field_eval. exact source_after.
Qed.
Lemma circuit_pass_output_link invalid modules top snapshot final instances instance parent module_id prefix suffix body output ground bits
 (instances_found:find_circuit_instances modules top=Some instances)
 (instance_found:SVM.find (instance::parent) instances=Some module_id)
 (module_found:find_module modules module_id=Some(FInmod module_id (prefix++Foutput output (Gtyp ground)::suffix) body))
 (suffix_frames:all(fun port=>port_identifier port != output)suffix=true)
 (node_frames:node_sync_check modules instances (instance::parent) output=true)
 (child_frames:child_only_check modules instances parent instance=true)
 (source_after:circuit_lookup (instance::parent) output final=Some(Gval ground bits))
 (ran:circuit_value_iter_with_memory_policy invalid modules top snapshot false=Some final) :
 circuit_interface parent instance output final=Some(Gval ground bits).
Proof.
 destruct (circuit_iteration_local_steps _ _ _ _ _ _ ran) as [actual [evaluated [Found [Synced Steps]]]].
 rewrite instances_found in Found. inversion Found;subst actual.
 rewrite (sync_circuit_preserves_lookup _ _ _ _ _ _ (node_sync_check_child _ _ _ _ node_frames) (node_sync_check_parent _ _ _ _ node_frames) Synced) in source_after.
 eapply sync_circuit_parent_output; [exact instance_found|exact module_found|exact suffix_frames| |exact(child_only_check_sound _ _ _ _ child_frames)|exact Synced].
 intros child_env found. unfold circuit_lookup in source_after. rewrite found in source_after. exact source_after.
Qed.
Lemma circuit_pass_input_type invalid modules top snapshot final instances instance parent module_id prefix suffix body input ground
 (instances_found:find_circuit_instances modules top=Some instances)
 (instance_found:SVM.find (instance::parent) instances=Some module_id)
 (module_found:find_module modules module_id=Some(FInmod module_id (prefix++Finput input (Gtyp ground)::suffix) body))
 (suffix_frames:all(child_port_frames input)suffix=true)
 (parent_frames:parent_only_check instances (instance::parent) input=true)
 (ran:circuit_value_iter_with_memory_policy invalid modules top snapshot false=Some final) :
 circuit_value_ground (instance::parent) input ground final.
Proof.
 destruct(circuit_iteration_local_steps _ _ _ _ _ _ ran)as[actual[evaluated[Found[Synced Steps]]]].
 rewrite instances_found in Found. inversion Found;subst actual.
 eapply sync_circuit_child_input_type;[exact instance_found|exact module_found|exact suffix_frames|exact(parent_only_check_sound _ _ _ parent_frames)|exact Synced].
Qed.
Lemma circuit_pass_output_type invalid modules top snapshot final instances instance parent module_id prefix suffix body output ground
 (instances_found:find_circuit_instances modules top=Some instances)
 (instance_found:SVM.find (instance::parent) instances=Some module_id)
 (module_found:find_module modules module_id=Some(FInmod module_id (prefix++Foutput output (Gtyp ground)::suffix) body))
 (suffix_frames:all(fun port=>port_identifier port != output)suffix=true)
 (child_frames:child_only_check modules instances parent instance=true)
 (ran:circuit_value_iter_with_memory_policy invalid modules top snapshot false=Some final) :
 circuit_interface_ground parent instance output ground final.
Proof.
 destruct(circuit_iteration_local_steps _ _ _ _ _ _ ran)as[actual[evaluated[Found[Synced Steps]]]].
 rewrite instances_found in Found. inversion Found;subst actual.
 eapply sync_circuit_parent_output_type;[exact instance_found|exact module_found|exact suffix_frames|exact(child_only_check_sound _ _ _ _ child_frames)|exact Synced].
Qed.
Print Assumptions circuit_pass_output_link.
