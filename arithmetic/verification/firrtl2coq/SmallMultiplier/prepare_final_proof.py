from pathlib import Path
H=Path(__file__).resolve().parent
s=r'''From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import HierarchyFacts.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalInstances GlobalProgressTypes PipelineInvariant GeneratedObservation ChildAssertions TopAssertions.
Module Tool:=SmallMultiplier.Model.
Local Open Scope N_scope.
Lemma circuit_value_environment path id states value
 (known:circuit_lookup path id states=Some value) :
 exists env,SVM.find path states=Some env /\ VM.find id env=Some value.
Proof.
 unfold circuit_lookup in known. destruct(SVM.find path states) as [env|] eqn:Found;[|discriminate].
 exists env. split;[reflexivity|exact known].
Qed.
'''
for a in [3,4]:
 s+=f'''Theorem all_top_assertions_{a} v states
 (sizes:global_leaf_sizes v) (invariant:pipeline_invariant v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 Tool.generated_assert_m3_{a}_all states.
Proof.
 have Root:=values 0%nat (ltac:(lia)).
 change(circuit_lookup [::] 0 states=Some(Gval Fclock(global_word_0 v))) in Root.
 destruct(circuit_value_environment _ _ _ _ Root) as [env [Found Value]].
 unfold Tool.generated_assert_m3_{a}_all. rewrite multiplier_instances_correct.
 apply assert_instances_from_members. intros path Member.
 let pairs:=eval vm_compute in (SVM.elements multiplier_instances) in change(List.In(path,3) pairs) in Member.
 cbn [List.In] in Member.
 repeat match goal with H:_ \\/ _ |- _ => destruct H as [H|H] end;try contradiction;
 inversion Member;subst;clear Member.
 rewrite Found. exact(top_assertion_{a} v states env sizes invariant values Found).
Qed.
'''
s += '''(* Names for the external proof conclusions, not assumed lemmas. *)
Definition obligation_0 : Prop := forall memory_init inputs (k : nat) states, generated_observe memory_init inputs k = Some states -> generated_legal_trace memory_init inputs k -> generated_assert_m0_0_all states.
Definition obligation_1 : Prop := forall memory_init inputs (k : nat) states, generated_observe memory_init inputs k = Some states -> generated_legal_trace memory_init inputs k -> generated_assert_m1_1_all states.
Definition obligation_2 : Prop := forall memory_init inputs (k : nat) states, generated_observe memory_init inputs k = Some states -> generated_legal_trace memory_init inputs k -> generated_assert_m2_2_all states.
Definition obligation_3 : Prop := forall memory_init inputs (k : nat) states, generated_observe memory_init inputs k = Some states -> generated_legal_trace memory_init inputs k -> generated_assert_m3_3_all states.
Definition obligation_4 : Prop := forall memory_init inputs (k : nat) states, generated_observe memory_init inputs k = Some states -> generated_legal_trace memory_init inputs k -> generated_assert_m3_4_all states.

'''
for i in range(5):
 s+=f'''Theorem multiplier_obligation_{i} : obligation_{i}.
Proof.
 intros contents inputs k states observed legal.
 destruct(generated_observation_values contents inputs k states observed legal) as [v [Sizes [Invariant Values]]].
 exact(all_{'child' if i<3 else 'top'}_assertions_{i} v states Sizes {'' if i<3 else 'Invariant '}Values).
Qed.
'''
s+='Theorem multiplier_all_obligations : '+' /\\ '.join(f'obligation_{i}' for i in range(5))+'.\nProof. exact(conj multiplier_obligation_0 (conj multiplier_obligation_1 (conj multiplier_obligation_2 (conj multiplier_obligation_3 multiplier_obligation_4)))). Qed.\nPrint Assumptions multiplier_all_obligations.\n'
(H/'Proof.v').write_text(s)
