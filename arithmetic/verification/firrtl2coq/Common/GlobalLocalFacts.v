From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import InstanceFoldFacts HierarchyFacts.

Lemma circuit_pass_local_value invalid modules top snapshot final set_regs instances path module_id ports stmts watched value
 (instances_found : find_circuit_instances modules top = Some instances)
 (module_found : SVM.find path instances = Some module_id)
 (body_found : find_module modules module_id = Some (FInmod module_id ports stmts))
 (memory_empty : memory_map_for_module modules module_id = Some empty_memory_map)
 (local_value : forall before after,
   SVM.find path snapshot = Some before ->
   value_iter_with_memory_policy (invalid path) empty_memory_map before set_regs before stmts = Some after ->
   VM.find watched after = Some value)
 (child_frames : forall p mi instance parent id ps body,
   SVM.find p instances = Some mi -> p = instance :: parent ->
   find_module modules mi = Some (FInmod id ps body) ->
   path = p -> all (child_port_frames watched) ps = true)
 (parent_frames : forall p mi instance parent,
   SVM.find p instances = Some mi -> p = instance :: parent ->
   path = parent -> instance != watched)
 (ran : circuit_value_iter_with_memory_policy invalid modules top snapshot set_regs = Some final) :
 circuit_lookup path watched final = Some value.
Proof.
 destruct (circuit_iteration_local_steps _ _ _ _ _ _ ran) as [actual [evaluated [Found [Synced Steps]]]].
 rewrite instances_found in Found. inversion Found; subst actual.
 destruct (Steps path module_id module_found) as [before [after [Before [Step After]]]].
 unfold local_instance_update in Step. rewrite Before body_found memory_empty in Step.
 rewrite (sync_circuit_preserves_lookup _ _ _ _ _ _ child_frames parent_frames Synced).
 unfold circuit_lookup. rewrite After. eapply local_value; eassumption.
Qed.
Print Assumptions circuit_pass_local_value.
