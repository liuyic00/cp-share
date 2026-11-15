From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
From Divider Require Import Model Stable Representation NodeProgress Initialization Bridge RuntimeRepresentation RuntimeInputs RuntimeState RuntimeSeed RuntimeReset AssertTransfer AssertClock ReferenceAssertions.
From Proofs Require Import RadixTrace.
Local Open Scope N_scope.
Definition reference_trace inputs k := Reference.run
 (Reference.step (seed_state (inputs O)) (runtime_inputs (reset_input (inputs O))))
 (fun j => runtime_inputs (inputs (S j))) k.
Local Opaque formal_state_after_reset circuit_formal_run circuit_formal_cycle Reference.step Reference.run.
Lemma generated_run_reference memory inputs k states
 (defined:formal_external_inputs_defined generated_modules generated_top (inputs O) = true)
 (defined_steps:forall j, (j < k)%coq_nat -> formal_external_inputs_defined generated_modules generated_top (inputs (S j)) = true)
 (ran:Tool.generated_run memory inputs k = Some states) :
 state_matches (reference_trace inputs k) states.
Proof.
 change (formal_run_after_reset generated_modules generated_top 1 (Fuint 1) memory inputs k = Some states) in ran.
 unfold formal_run_after_reset in ran.
 destruct (formal_state_after_reset generated_modules generated_top 1 (Fuint 1) memory (inputs O)) as [initial|] eqn:Initial; [|discriminate].
 unfold reference_trace. eapply runtime_run; [eapply runtime_reset; eassumption|exact defined_steps|exact ran].
Qed.
Lemma reference_trace_asserts inputs k :
 Reference.asserts (reference_trace inputs k) (runtime_inputs (inputs (S k))).
Proof.
 unfold reference_trace. apply RadixTrace.all_assertions_after_reset. apply reset_input_high.
Qed.
Local Opaque circuit_initial_map_with_memory circuit_iter_count_with_memory circuit_formal_iterations.
Lemma observe_cycle_matches previous inputs : Tool.generated_observe_cycle previous inputs = divider_observe_cycle (Some previous) inputs.
Proof. unfold Tool.generated_observe_cycle, divider_observe_cycle. rewrite generated_modules_match generated_top_match. reflexivity. Qed.
Local Opaque Tool.generated_run Tool.generated_observe_cycle divider_observe_cycle.
Lemma generated_observation_reference memory inputs k states
 (observed:Tool.generated_observe memory inputs k = Some states)
 (legal:Tool.generated_legal_trace memory inputs k) :
 exists env ghost, SVM.find [::] states = Some env /\ (forall id, divider_domain id -> VM.find id env = VM.find id (stable_env (runtime_leaves (reference_trace inputs k) (inputs (S k)) ghost))).
Proof.
 destruct legal as [Defined Legal].
 have DefinedSteps : forall j, (j < k)%coq_nat -> formal_external_inputs_defined generated_modules generated_top (inputs (S j)) = true.
 { intros j Less. exact (proj1 (Legal j (Nat.lt_le_incl _ _ Less))). }
 have DefinedCurrent : formal_external_inputs_defined generated_modules generated_top (inputs (S k)) = true := proj1 (Legal k (Nat.le_refl k)).
 unfold Tool.generated_observe in observed.
 destruct (Tool.generated_run memory inputs k) as [previous|] eqn:Ran; [|discriminate].
 destruct (generated_run_reference memory inputs k previous Defined DefinedSteps Ran) as [old [ghost [Found Registers]]].
 rewrite observe_cycle_matches in observed.
 change (divider_observe_cycle (Some previous) (inputs (S k)) = Some states) in observed.
 destruct (divider_observation_values (runtime_leaves (reference_trace inputs k) (inputs (S k)) ghost)
 previous old (inputs (S k)) states
 (runtime_leaf_sizes _ _ _ DefinedCurrent) Found
 (registers_runtime _ _ _ _ Registers)
 (runtime_port_values _ _ _ DefinedCurrent) observed) as [env [Final Values]].
 exists env,ghost. split; assumption.
Qed.
Theorem divider_obligation_0 : Tool.obligation_0.
Proof.
 intros memory inputs k states observed legal.
 destruct (generated_observation_reference memory inputs k states observed legal) as [env [ghost [Found Values]]].
 apply (proj2 (assertion_0_instance states env Found)).
 apply (proj2 (assertion_0_local_transfer env _ Values)).
 unfold runtime_leaves.
 apply (proj2 (assertion_0_local_clock _ _)).
 apply reference_assertion_0. apply reference_trace_asserts.
Qed.
Theorem divider_obligation_1 : Tool.obligation_1.
Proof.
 intros memory inputs k states observed legal.
 destruct (generated_observation_reference memory inputs k states observed legal) as [env [ghost [Found Values]]].
 apply (proj2 (assertion_1_instance states env Found)).
 apply (proj2 (assertion_1_local_transfer env _ Values)).
 unfold runtime_leaves.
 apply (proj2 (assertion_1_local_clock _ _)).
 apply reference_assertion_1. apply reference_trace_asserts.
Qed.
Theorem divider_obligation_2 : Tool.obligation_2.
Proof.
 intros memory inputs k states observed legal.
 destruct (generated_observation_reference memory inputs k states observed legal) as [env [ghost [Found Values]]].
 apply (proj2 (assertion_2_instance states env Found)).
 apply (proj2 (assertion_2_local_transfer env _ Values)).
 unfold runtime_leaves.
 apply (proj2 (assertion_2_local_clock _ _)).
 apply reference_assertion_2. apply reference_trace_asserts.
Qed.
Theorem divider_obligation_3 : Tool.obligation_3.
Proof.
 intros memory inputs k states observed legal.
 destruct (generated_observation_reference memory inputs k states observed legal) as [env [ghost [Found Values]]].
 apply (proj2 (assertion_3_instance states env Found)).
 apply (proj2 (assertion_3_local_transfer env _ Values)).
 unfold runtime_leaves.
 apply (proj2 (assertion_3_local_clock _ _)).
 apply reference_assertion_3. apply reference_trace_asserts.
Qed.
Theorem divider_obligation_4 : Tool.obligation_4.
Proof.
 intros memory inputs k states observed legal.
 destruct (generated_observation_reference memory inputs k states observed legal) as [env [ghost [Found Values]]].
 apply (proj2 (assertion_4_instance states env Found)).
 apply (proj2 (assertion_4_local_transfer env _ Values)).
 unfold runtime_leaves.
 apply (proj2 (assertion_4_local_clock _ _)).
 apply reference_assertion_4. apply reference_trace_asserts.
Qed.
Theorem divider_obligation_5 : Tool.obligation_5.
Proof.
 intros memory inputs k states observed legal.
 destruct (generated_observation_reference memory inputs k states observed legal) as [env [ghost [Found Values]]].
 apply (proj2 (assertion_5_instance states env Found)).
 apply (proj2 (assertion_5_local_transfer env _ Values)).
 unfold runtime_leaves.
 apply (proj2 (assertion_5_local_clock _ _)).
 apply reference_assertion_5. apply reference_trace_asserts.
Qed.
Theorem divider_obligation_6 : Tool.obligation_6.
Proof.
 intros memory inputs k states observed legal.
 destruct (generated_observation_reference memory inputs k states observed legal) as [env [ghost [Found Values]]].
 apply (proj2 (assertion_6_instance states env Found)).
 apply (proj2 (assertion_6_local_transfer env _ Values)).
 unfold runtime_leaves.
 apply (proj2 (assertion_6_local_clock _ _)).
 apply reference_assertion_6. apply reference_trace_asserts.
Qed.
Theorem divider_obligation_7 : Tool.obligation_7.
Proof.
 intros memory inputs k states observed legal.
 destruct (generated_observation_reference memory inputs k states observed legal) as [env [ghost [Found Values]]].
 apply (proj2 (assertion_7_instance states env Found)).
 apply (proj2 (assertion_7_local_transfer env _ Values)).
 unfold runtime_leaves.
 apply (proj2 (assertion_7_local_clock _ _)).
 apply reference_assertion_7. apply reference_trace_asserts.
Qed.
Theorem divider_obligation_8 : Tool.obligation_8.
Proof.
 intros memory inputs k states observed legal.
 destruct (generated_observation_reference memory inputs k states observed legal) as [env [ghost [Found Values]]].
 apply (proj2 (assertion_8_instance states env Found)).
 apply (proj2 (assertion_8_local_transfer env _ Values)).
 unfold runtime_leaves.
 apply (proj2 (assertion_8_local_clock _ _)).
 apply reference_assertion_8. apply reference_trace_asserts.
Qed.
Theorem divider_obligation_9 : Tool.obligation_9.
Proof.
 intros memory inputs k states observed legal.
 destruct (generated_observation_reference memory inputs k states observed legal) as [env [ghost [Found Values]]].
 apply (proj2 (assertion_9_instance states env Found)).
 apply (proj2 (assertion_9_local_transfer env _ Values)).
 unfold runtime_leaves.
 apply (proj2 (assertion_9_local_clock _ _)).
 apply reference_assertion_9. apply reference_trace_asserts.
Qed.
Theorem divider_obligation_10 : Tool.obligation_10.
Proof.
 intros memory inputs k states observed legal.
 destruct (generated_observation_reference memory inputs k states observed legal) as [env [ghost [Found Values]]].
 apply (proj2 (assertion_10_instance states env Found)).
 apply (proj2 (assertion_10_local_transfer env _ Values)).
 unfold runtime_leaves.
 apply (proj2 (assertion_10_local_clock _ _)).
 apply reference_assertion_10. apply reference_trace_asserts.
Qed.
Print Assumptions divider_obligation_0.
Print Assumptions divider_obligation_10.
