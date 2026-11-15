From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import HierarchyFacts.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalInstances GlobalProgressTypes PipelineInvariant GeneratedObservation ChildAssertions TopAssertions.
Module Tool:=ArithmeticFIRRTL.ArrayMulDataModule8.
Local Open Scope N_scope.
Lemma circuit_value_environment path id states value
 (known:circuit_lookup path id states=Some value) :
 exists env,SVM.find path states=Some env /\ VM.find id env=Some value.
Proof.
 unfold circuit_lookup in known. destruct(SVM.find path states) as [env|] eqn:Found;[|discriminate].
 exists env. split;[reflexivity|exact known].
Qed.
Theorem all_top_assertions_3 v states
 (sizes:global_leaf_sizes v) (invariant:pipeline_invariant v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 Tool.generated_assert_m3_3_all states.
Proof.
 have Root:=values 0%nat (ltac:(lia)).
 change(circuit_lookup [::] 0 states=Some(Gval Fclock(global_word_0 v))) in Root.
 destruct(circuit_value_environment _ _ _ _ Root) as [env [Found Value]].
 unfold Tool.generated_assert_m3_3_all. rewrite generated_modules_match generated_top_match multiplier_instances_correct.
 apply assert_instances_from_members. intros path Member.
 let pairs:=eval vm_compute in (SVM.elements multiplier_instances) in change(List.In(path,3) pairs) in Member.
 cbn [List.In] in Member.
 repeat match goal with H:_ \/ _ |- _ => destruct H as [H|H] end;try contradiction;
 inversion Member;subst;clear Member.
 rewrite Found. exact(top_assertion_3 v states env sizes invariant values Found).
Qed.
Theorem all_top_assertions_4 v states
 (sizes:global_leaf_sizes v) (invariant:pipeline_invariant v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 Tool.generated_assert_m3_4_all states.
Proof.
 have Root:=values 0%nat (ltac:(lia)).
 change(circuit_lookup [::] 0 states=Some(Gval Fclock(global_word_0 v))) in Root.
 destruct(circuit_value_environment _ _ _ _ Root) as [env [Found Value]].
 unfold Tool.generated_assert_m3_4_all. rewrite generated_modules_match generated_top_match multiplier_instances_correct.
 apply assert_instances_from_members. intros path Member.
 let pairs:=eval vm_compute in (SVM.elements multiplier_instances) in change(List.In(path,3) pairs) in Member.
 cbn [List.In] in Member.
 repeat match goal with H:_ \/ _ |- _ => destruct H as [H|H] end;try contradiction;
 inversion Member;subst;clear Member.
 rewrite Found. exact(top_assertion_4 v states env sizes invariant values Found).
Qed.
Theorem multiplier_obligation_0 : Tool.obligation_0.
Proof.
 intros contents inputs k states observed legal.
 destruct(generated_observation_values contents inputs k states observed legal) as [v [Sizes [Invariant Values]]].
 exact(all_child_assertions_0 v states Sizes Values).
Qed.
Theorem multiplier_obligation_1 : Tool.obligation_1.
Proof.
 intros contents inputs k states observed legal.
 destruct(generated_observation_values contents inputs k states observed legal) as [v [Sizes [Invariant Values]]].
 exact(all_child_assertions_1 v states Sizes Values).
Qed.
Theorem multiplier_obligation_2 : Tool.obligation_2.
Proof.
 intros contents inputs k states observed legal.
 destruct(generated_observation_values contents inputs k states observed legal) as [v [Sizes [Invariant Values]]].
 exact(all_child_assertions_2 v states Sizes Values).
Qed.
Theorem multiplier_obligation_3 : Tool.obligation_3.
Proof.
 intros contents inputs k states observed legal.
 destruct(generated_observation_values contents inputs k states observed legal) as [v [Sizes [Invariant Values]]].
 exact(all_top_assertions_3 v states Sizes Invariant Values).
Qed.
Theorem multiplier_obligation_4 : Tool.obligation_4.
Proof.
 intros contents inputs k states observed legal.
 destruct(generated_observation_values contents inputs k states observed legal) as [v [Sizes [Invariant Values]]].
 exact(all_top_assertions_4 v states Sizes Invariant Values).
Qed.
Theorem multiplier_all_obligations : Tool.obligation_0 /\ Tool.obligation_1 /\ Tool.obligation_2 /\ Tool.obligation_3 /\ Tool.obligation_4.
Proof. exact(conj multiplier_obligation_0 (conj multiplier_obligation_1 (conj multiplier_obligation_2 (conj multiplier_obligation_3 multiplier_obligation_4)))). Qed.
Print Assumptions multiplier_all_obligations.
