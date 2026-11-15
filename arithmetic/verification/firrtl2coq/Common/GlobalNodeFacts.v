From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import StatementFacts InstanceFoldFacts HierarchyFacts.

Lemma circuit_pass_node_value invalid modules top snapshot final instances path module_id ports stmts watched expr ground bits
 (instances_found : find_circuit_instances modules top = Some instances)
 (module_found : SVM.find path instances = Some module_id)
 (body_found : find_module modules module_id = Some (FInmod module_id ports stmts))
 (memory_empty : memory_map_for_module modules module_id = Some empty_memory_map)
 (certificate : node_certificate watched expr stmts)
 (not_register : registers_frame watched stmts = true)
 (evaluates : forall old, SVM.find path snapshot = Some old ->
   eval_hfexpr_with_memory empty_memory_map expr old old = Some (Gval ground bits))
 (child_frames : forall p mi instance parent id ps body,
   SVM.find p instances = Some mi -> p = instance :: parent ->
   find_module modules mi = Some (FInmod id ps body) ->
   path = p -> all (child_port_frames watched) ps = true)
 (parent_frames : forall p mi instance parent,
   SVM.find p instances = Some mi -> p = instance :: parent ->
   path = parent -> instance != watched)
 (ran : circuit_value_iter_with_memory_policy invalid modules top snapshot false = Some final) :
 circuit_lookup path watched final = Some (Gval ground bits).
Proof.
 destruct (circuit_iteration_local_steps _ _ _ _ _ _ ran) as [actual [evaluated [Found [Synced Steps]]]].
 rewrite instances_found in Found. inversion Found; subst actual.
 destruct (Steps path module_id module_found) as [before [after [Before [Step After]]]].
 unfold local_instance_update in Step. rewrite Before body_found memory_empty in Step.
 have Node : VM.find watched after = Some (Gval ground bits).
 { eapply pass_node_value; [exact certificate|exact not_register|apply evaluates; exact Before|exact Step]. }
 rewrite (sync_circuit_preserves_lookup _ _ _ _ _ _ child_frames parent_frames Synced).
 unfold circuit_lookup. rewrite After. exact Node.
Qed.
Print Assumptions circuit_pass_node_value.
