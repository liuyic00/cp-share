From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import InstanceFoldFacts InitialMapFacts.
From Divider Require Import Model.
Local Open Scope N_scope.
Definition divider_instances : SVM.t VarOrder.T := SVM.add [::] 0 (SVM.empty VarOrder.T).
Lemma divider_instances_computed :
 find_circuit_instances generated_modules generated_top = Some divider_instances.
Proof. vm_compute. reflexivity. Qed.
Lemma divider_empty_memory : memory_map_for_module generated_modules 0 = Some empty_memory_map.
Proof. vm_compute. reflexivity. Qed.
Lemma divider_iteration_local invalid states set_regs final
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top states set_regs = Some final) :
 exists before after, SVM.find [::] states = Some before /\
 value_iter_with_memory_policy (invalid [::]) empty_memory_map before set_regs before generated_module_0_stmts_0 = Some after /\
 SVM.find [::] final = Some after.
Proof.
 destruct (circuit_iteration_local_steps _ _ _ _ _ _ ran) as [instances [evaluated [Instances [Synced Steps]]]].
 rewrite divider_instances_computed in Instances. inversion Instances; subst instances.
 change (Some evaluated = Some final) in Synced. inversion Synced; subst evaluated.
 destruct (Steps [::] 0 (Logic.eq_refl _)) as [before [after [Before [Ran After]]]].
 exists before, after. split; [exact Before|]. split; [|exact After].
 unfold local_instance_update in Ran. rewrite Before divider_empty_memory in Ran.
 exact Ran.
Qed.
Print Assumptions divider_iteration_local.
Definition divider_ports := match generated_module_0 with
 | FInmod _ ports _ => ports | _ => [::] end.
Lemma divider_initial_local previous external states
 (ran : circuit_initial_map_with_memory generated_modules generated_top previous external = Some states) :
 exists declared env,
 statements_initial_map_with_memory generated_modules generated_module_0_stmts_0
   (match previous with Some maps => SVM.find [::] maps | None => None end)
   (ports_initial_map divider_ports) = Some declared /\
 update_external_ports declared external divider_ports = Some env /\
 SVM.find [::] states = Some env.
Proof.
 eapply single_module_initial_local; [exact divider_instances_computed|reflexivity|exact ran].
Qed.
Print Assumptions divider_initial_local.
