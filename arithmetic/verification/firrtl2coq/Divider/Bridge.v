From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From Divider Require Import Model Stable SingleModule NodeProgress Initialization Convergence Commit.
Local Open Scope N_scope.
Definition divider_iteration_bound : nat := Eval vm_compute in
 match circuit_iter_count_with_memory generated_modules generated_top Gtyp_connect_count with
 | Some count => count | None => O end.
Lemma divider_iteration_bound_computed :
 circuit_iter_count_with_memory generated_modules generated_top Gtyp_connect_count = Some divider_iteration_bound.
Proof. vm_compute. reflexivity. Qed.
Lemma divider_iteration_bound_sufficient : Nat.le 25 divider_iteration_bound.
Proof. vm_compute. repeat constructor. Qed.
(* This is the generated before-edge observation expression, using the original
   initializer and original circuit_formal_iterations, with no register commit. *)
Definition divider_observe_cycle previous inputs :=
 match circuit_initial_map_with_memory generated_modules generated_top previous (formal_external_inputs inputs),
       circuit_iter_count_with_memory generated_modules generated_top Gtyp_connect_count with
 | Some initial, Some count => circuit_formal_iterations generated_modules generated_top inputs count initial
 | _, _ => None end.
Definition divider_leaves_sized (v : leaf_values) : Prop :=
 size (v 0) = 1%nat /\
 size (v 1) = 1%nat /\
 size (v 3) = 1%nat /\
 size (v 4) = 64%nat /\
 size (v 5) = 64%nat /\
 size (v 6) = 64%nat /\
 size (v 7) = 1%nat /\
 size (v 10) = 1%nat /\
 size (v 11) = 1%nat /\
 size (v 12) = 1%nat /\
 size (v 13) = 3%nat /\
 size (v 18) = 1%nat /\
 size (v 20) = 129%nat /\
 size (v 33) = 1%nat /\
 size (v 38) = 1%nat /\
 size (v 40) = 64%nat /\
 size (v 43) = 65%nat /\
 size (v 45) = 1%nat /\
 size (v 46) = 1%nat /\
 size (v 47) = 1%nat /\
 size (v 51) = 6%nat /\
 size (v 445) = 1%nat /\
 size (v 446) = 3%nat /\
 size (v 447) = 6%nat /\
 size (v 475) = 1%nat /\
 size (v 476) = 64%nat.
Lemma divider_settled_values v previous old inputs initial settled
 (sized : divider_leaves_sized v)
 (old_found : SVM.find [::] previous = Some old)
 (registers : divider_register_values v old)
 (ports : divider_input_values v (formal_external_inputs inputs))
 (initialized : circuit_initial_map_with_memory generated_modules generated_top (Some previous) (formal_external_inputs inputs) = Some initial)
 (iterations : circuit_formal_iterations generated_modules generated_top inputs divider_iteration_bound initial = Some settled) :
 exists env, SVM.find [::] settled = Some env /\
 (forall id, divider_domain id -> VM.find id env = VM.find id (stable_env v)).
Proof.
 destruct sized as [size_0 [size_1 [size_3 [size_4 [size_5 [size_6 [size_7 [size_10 [size_11 [size_12 [size_13 [size_18 [size_20 [size_33 [size_38 [size_40 [size_43 [size_45 [size_46 [size_47 [size_51 [size_445 [size_446 [size_447 [size_475 size_476]]]]]]]]]]]]]]]]]]]]]]]]].
 have Init := divider_initial_ranked v previous old (formal_external_inputs inputs) initial old_found registers ports initialized.
 have Ranked : divider_circuit_ranked v O initial by exact Init.
 have Result : exists env, SVM.find [::] settled = Some env /\
 (forall id, divider_domain id -> VM.find id env = VM.find id (stable_env v)) /\ divider_output_types env.
 { eapply divider_iterations_converge; try eassumption; exact divider_iteration_bound_sufficient. }
 destruct Result as [env [Found [Values Types]]]. exists env. split; assumption.
Qed.
Local Opaque circuit_initial_map_with_memory circuit_formal_iterations circuit_value_iter_with_memory_policy.
Lemma divider_observation_values v previous old inputs observed
 (sized : divider_leaves_sized v)
 (old_found : SVM.find [::] previous = Some old)
 (registers : divider_register_values v old)
 (ports : divider_input_values v (formal_external_inputs inputs))
 (observed_ok : divider_observe_cycle (Some previous) inputs = Some observed) :
 exists env, SVM.find [::] observed = Some env /\
 (forall id, divider_domain id -> VM.find id env = VM.find id (stable_env v)).
Proof.
 unfold divider_observe_cycle in observed_ok. rewrite divider_iteration_bound_computed in observed_ok.
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some previous) (formal_external_inputs inputs)) as [initial|] eqn:Initialized; try discriminate.
 eapply divider_settled_values; eassumption.
Qed.
Lemma divider_cycle_values v previous old inputs final
 (sized : divider_leaves_sized v)
 (old_found : SVM.find [::] previous = Some old)
 (registers : divider_register_values v old)
 (ports : divider_input_values v (formal_external_inputs inputs))
 (ran : circuit_formal_cycle generated_modules generated_top (Some previous) inputs = Some final) :
 exists env, SVM.find [::] final = Some env /\ divider_committed v env.
Proof.
 unfold circuit_formal_cycle in ran. rewrite divider_iteration_bound_computed in ran.
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some previous) (formal_external_inputs inputs)) as [initial|] eqn:Initialized; try discriminate.
 destruct (circuit_formal_iterations generated_modules generated_top inputs divider_iteration_bound initial) as [settled|] eqn:Iterations; try discriminate.
 destruct (divider_settled_values v previous old inputs initial settled sized old_found registers ports Initialized Iterations) as [env [Found Values]].
 destruct (divider_iteration_local _ _ _ _ ran) as [before [after [Before [Step After]]]].
 rewrite Found in Before. inversion Before; subst before.
 exists after. split; [exact After|]. eapply divider_commit_values; eassumption.
Qed.
Print Assumptions divider_observation_values.
Print Assumptions divider_cycle_values.
