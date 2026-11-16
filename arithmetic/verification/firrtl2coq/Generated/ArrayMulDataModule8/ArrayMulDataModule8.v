From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_for_circuit Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
From SmallMultiplier Require Import Model.
From SmallMultiplier Require Proof.

Lemma generated_assert_0 : forall memory_init inputs (k : nat) states, generated_observe memory_init inputs k = Some states -> generated_legal_trace memory_init inputs k -> generated_assert_m0_0_all states.
Proof. exact SmallMultiplier.Proof.multiplier_obligation_0. Qed.
Lemma generated_assert_1 : forall memory_init inputs (k : nat) states, generated_observe memory_init inputs k = Some states -> generated_legal_trace memory_init inputs k -> generated_assert_m1_1_all states.
Proof. exact SmallMultiplier.Proof.multiplier_obligation_1. Qed.
Lemma generated_assert_2 : forall memory_init inputs (k : nat) states, generated_observe memory_init inputs k = Some states -> generated_legal_trace memory_init inputs k -> generated_assert_m2_2_all states.
Proof. exact SmallMultiplier.Proof.multiplier_obligation_2. Qed.
Lemma generated_assert_3 : forall memory_init inputs (k : nat) states, generated_observe memory_init inputs k = Some states -> generated_legal_trace memory_init inputs k -> generated_assert_m3_3_all states.
Proof. exact SmallMultiplier.Proof.multiplier_obligation_3. Qed.
Lemma generated_assert_4 : forall memory_init inputs (k : nat) states, generated_observe memory_init inputs k = Some states -> generated_legal_trace memory_init inputs k -> generated_assert_m3_4_all states.
Proof. exact SmallMultiplier.Proof.multiplier_obligation_4. Qed.
