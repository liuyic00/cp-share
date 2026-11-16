From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_for_circuit Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
From Divider Require Import Model.
From Divider Require Proof.

Lemma generated_assert_0 : forall memory_init inputs (k : nat) states, generated_observe memory_init inputs k = Some states -> generated_legal_trace memory_init inputs k -> generated_assert_m0_0_all states.
Proof. exact Divider.Proof.divider_obligation_0. Qed.
Lemma generated_assert_1 : forall memory_init inputs (k : nat) states, generated_observe memory_init inputs k = Some states -> generated_legal_trace memory_init inputs k -> generated_assert_m0_1_all states.
Proof. exact Divider.Proof.divider_obligation_1. Qed.
Lemma generated_assert_2 : forall memory_init inputs (k : nat) states, generated_observe memory_init inputs k = Some states -> generated_legal_trace memory_init inputs k -> generated_assert_m0_2_all states.
Proof. exact Divider.Proof.divider_obligation_2. Qed.
Lemma generated_assert_3 : forall memory_init inputs (k : nat) states, generated_observe memory_init inputs k = Some states -> generated_legal_trace memory_init inputs k -> generated_assert_m0_3_all states.
Proof. exact Divider.Proof.divider_obligation_3. Qed.
Lemma generated_assert_4 : forall memory_init inputs (k : nat) states, generated_observe memory_init inputs k = Some states -> generated_legal_trace memory_init inputs k -> generated_assert_m0_4_all states.
Proof. exact Divider.Proof.divider_obligation_4. Qed.
Lemma generated_assert_5 : forall memory_init inputs (k : nat) states, generated_observe memory_init inputs k = Some states -> generated_legal_trace memory_init inputs k -> generated_assert_m0_5_all states.
Proof. exact Divider.Proof.divider_obligation_5. Qed.
Lemma generated_assert_6 : forall memory_init inputs (k : nat) states, generated_observe memory_init inputs k = Some states -> generated_legal_trace memory_init inputs k -> generated_assert_m0_6_all states.
Proof. exact Divider.Proof.divider_obligation_6. Qed.
Lemma generated_assert_7 : forall memory_init inputs (k : nat) states, generated_observe memory_init inputs k = Some states -> generated_legal_trace memory_init inputs k -> generated_assert_m0_7_all states.
Proof. exact Divider.Proof.divider_obligation_7. Qed.
Lemma generated_assert_8 : forall memory_init inputs (k : nat) states, generated_observe memory_init inputs k = Some states -> generated_legal_trace memory_init inputs k -> generated_assert_m0_8_all states.
Proof. exact Divider.Proof.divider_obligation_8. Qed.
Lemma generated_assert_9 : forall memory_init inputs (k : nat) states, generated_observe memory_init inputs k = Some states -> generated_legal_trace memory_init inputs k -> generated_assert_m0_9_all states.
Proof. exact Divider.Proof.divider_obligation_9. Qed.
Lemma generated_assert_10 : forall memory_init inputs (k : nat) states, generated_observe memory_init inputs k = Some states -> generated_legal_trace memory_init inputs k -> generated_assert_m0_10_all states.
Proof. exact Divider.Proof.divider_obligation_10. Qed.
