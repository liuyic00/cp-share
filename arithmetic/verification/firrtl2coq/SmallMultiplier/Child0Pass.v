From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import StatementFacts ScalarEvaluation.
From SmallMultiplier Require Import Model NodeCertificateCheck Child0Stable Child0Local.
Local Open Scope N_scope.
Lemma node_6_certificate : node_certificate 6 expr_word_6 generated_module_0_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_6 invalid v old before after
 (H0 : VM.find 2 old = Some (Gval (Fuint 1) (word_2 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_0_stmts_0 = Some after) :
 VM.find 6 after = Some (Gval (Fuint 4) (word_6 v)).
Proof. eapply pass_node_value; [exact node_6_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_6_value; assumption. Qed.
Lemma node_7_certificate : node_certificate 7 expr_word_7 generated_module_0_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_7 invalid v old before after
 (H0 : VM.find 3 old = Some (Gval (Fuint 1) (word_3 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_0_stmts_0 = Some after) :
 VM.find 7 after = Some (Gval (Fuint 4) (word_7 v)).
Proof. eapply pass_node_value; [exact node_7_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_7_value; assumption. Qed.
Lemma node_8_certificate : node_certificate 8 expr_word_8 generated_module_0_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_8 invalid v old before after
 (H0 : VM.find 6 old = Some (Gval (Fuint 4) (word_6 v)))
 (H1 : VM.find 7 old = Some (Gval (Fuint 4) (word_7 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_0_stmts_0 = Some after) :
 VM.find 8 after = Some (Gval (Fuint 5) (word_8 v)).
Proof. eapply pass_node_value; [exact node_8_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_8_value; assumption. Qed.
Lemma node_9_certificate : node_certificate 9 expr_word_9 generated_module_0_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_9 invalid v old before after
 (H0 : VM.find 8 old = Some (Gval (Fuint 5) (word_8 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_0_stmts_0 = Some after) :
 VM.find 9 after = Some (Gval (Fuint 4) (word_9 v)).
Proof. eapply pass_node_value; [exact node_9_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_9_value; assumption. Qed.
Lemma node_10_certificate : node_certificate 10 expr_word_10 generated_module_0_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_10 invalid v old before after
 (H0 : VM.find 4 old = Some (Gval (Fuint 1) (word_4 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_0_stmts_0 = Some after) :
 VM.find 10 after = Some (Gval (Fuint 4) (word_10 v)).
Proof. eapply pass_node_value; [exact node_10_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_10_value; assumption. Qed.
Lemma node_11_certificate : node_certificate 11 expr_word_11 generated_module_0_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_11 invalid v old before after
 (H0 : VM.find 5 old = Some (Gval (Fuint 1) (word_5 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_0_stmts_0 = Some after) :
 VM.find 11 after = Some (Gval (Fuint 4) (word_11 v)).
Proof. eapply pass_node_value; [exact node_11_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_11_value; assumption. Qed.
Lemma node_12_certificate : node_certificate 12 expr_word_12 generated_module_0_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_12 invalid v old before after
 (H0 : VM.find 11 old = Some (Gval (Fuint 4) (word_11 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_0_stmts_0 = Some after) :
 VM.find 12 after = Some (Gval (Fuint 5) (word_12 v)).
Proof. eapply pass_node_value; [exact node_12_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_12_value; assumption. Qed.
Lemma node_13_certificate : node_certificate 13 expr_word_13 generated_module_0_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_13 invalid v old before after
 (H0 : VM.find 10 old = Some (Gval (Fuint 4) (word_10 v)))
 (H1 : VM.find 12 old = Some (Gval (Fuint 5) (word_12 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_0_stmts_0 = Some after) :
 VM.find 13 after = Some (Gval (Fuint 6) (word_13 v)).
Proof. eapply pass_node_value; [exact node_13_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_13_value; assumption. Qed.
Lemma node_14_certificate : node_certificate 14 expr_word_14 generated_module_0_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_14 invalid v old before after
 (H0 : VM.find 13 old = Some (Gval (Fuint 6) (word_13 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_0_stmts_0 = Some after) :
 VM.find 14 after = Some (Gval (Fuint 5) (word_14 v)).
Proof. eapply pass_node_value; [exact node_14_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_14_value; assumption. Qed.
Lemma node_15_certificate : node_certificate 15 expr_word_15 generated_module_0_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_15 invalid v old before after
 (H0 : VM.find 9 old = Some (Gval (Fuint 4) (word_9 v)))
 (H1 : VM.find 14 old = Some (Gval (Fuint 5) (word_14 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_0_stmts_0 = Some after) :
 VM.find 15 after = Some (Gval (Fuint 1) (word_15 v)).
Proof. eapply pass_node_value; [exact node_15_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_15_value; assumption. Qed.
Lemma node_16_certificate : node_certificate 16 expr_word_16 generated_module_0_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_16 invalid v old before after
 (H0 : VM.find 1 old = Some (Gval (Fuint 1) (word_1 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_0_stmts_0 = Some after) :
 VM.find 16 after = Some (Gval (Fuint 1) (word_16 v)).
Proof. eapply pass_node_value; [exact node_16_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_16_value; assumption. Qed.
Lemma node_17_certificate : node_certificate 17 expr_word_17 generated_module_0_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_17 invalid v old before after
 (H0 : VM.find 16 old = Some (Gval (Fuint 1) (word_16 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_0_stmts_0 = Some after) :
 VM.find 17 after = Some (Gval (Fuint 1) (word_17 v)).
Proof. eapply pass_node_value; [exact node_17_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_17_value; assumption. Qed.
Lemma node_18_certificate : node_certificate 18 expr_word_18 generated_module_0_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_18 invalid v old before after
 (H0 : VM.find 15 old = Some (Gval (Fuint 1) (word_15 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_0_stmts_0 = Some after) :
 VM.find 18 after = Some (Gval (Fuint 1) (word_18 v)).
Proof. eapply pass_node_value; [exact node_18_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_18_value; assumption. Qed.
Lemma node_19_certificate : node_certificate 19 expr_word_19 generated_module_0_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_19 invalid v old before after
 (H0 : VM.find 2 old = Some (Gval (Fuint 1) (word_2 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_0_stmts_0 = Some after) :
 VM.find 19 after = Some (Gval (Fuint 1) (word_19 v)).
Proof. eapply pass_node_value; [exact node_19_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_19_value; assumption. Qed.
Lemma node_20_certificate : node_certificate 20 expr_word_20 generated_module_0_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_20 invalid v old before after
 (H0 : VM.find 3 old = Some (Gval (Fuint 1) (word_3 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_0_stmts_0 = Some after) :
 VM.find 20 after = Some (Gval (Fuint 1) (word_20 v)).
Proof. eapply pass_node_value; [exact node_20_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_20_value; assumption. Qed.
Lemma node_21_certificate : node_certificate 21 expr_word_21 generated_module_0_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_21 invalid v old before after
 (H0 : VM.find 19 old = Some (Gval (Fuint 1) (word_19 v)))
 (H1 : VM.find 20 old = Some (Gval (Fuint 1) (word_20 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_0_stmts_0 = Some after) :
 VM.find 21 after = Some (Gval (Fuint 1) (word_21 v)).
Proof. eapply pass_node_value; [exact node_21_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_21_value; assumption. Qed.
Lemma node_22_certificate : node_certificate 22 expr_word_22 generated_module_0_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_22 invalid v old before after
 (H0 : VM.find 19 old = Some (Gval (Fuint 1) (word_19 v)))
 (H1 : VM.find 20 old = Some (Gval (Fuint 1) (word_20 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_0_stmts_0 = Some after) :
 VM.find 22 after = Some (Gval (Fuint 1) (word_22 v)).
Proof. eapply pass_node_value; [exact node_22_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_22_value; assumption. Qed.
Lemma node_23_certificate : node_certificate 23 expr_word_23 generated_module_0_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_23 invalid v old before after
 (H0 : VM.find 21 old = Some (Gval (Fuint 1) (word_21 v)))
 (H1 : VM.find 22 old = Some (Gval (Fuint 1) (word_22 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_0_stmts_0 = Some after) :
 VM.find 23 after = Some (Gval (Fuint 2) (word_23 v)).
Proof. eapply pass_node_value; [exact node_23_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_23_value; assumption. Qed.
Lemma node_24_certificate : node_certificate 24 expr_word_24 generated_module_0_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_24 invalid v old before after
 (H0 : VM.find 23 old = Some (Gval (Fuint 2) (word_23 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_0_stmts_0 = Some after) :
 VM.find 24 after = Some (Gval (Fuint 2) (word_24 v)).
Proof. eapply pass_node_value; [exact node_24_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_24_value; assumption. Qed.
Lemma node_25_certificate : node_certificate 25 expr_word_25 generated_module_0_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_25 invalid v old before after
 (H0 : VM.find 24 old = Some (Gval (Fuint 2) (word_24 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_0_stmts_0 = Some after) :
 VM.find 25 after = Some (Gval (Fuint 1) (word_25 v)).
Proof. eapply pass_node_value; [exact node_25_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_25_value; assumption. Qed.
Lemma node_26_certificate : node_certificate 26 expr_word_26 generated_module_0_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_26 invalid v old before after
 (H0 : VM.find 24 old = Some (Gval (Fuint 2) (word_24 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_0_stmts_0 = Some after) :
 VM.find 26 after = Some (Gval (Fuint 1) (word_26 v)).
Proof. eapply pass_node_value; [exact node_26_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_26_value; assumption. Qed.
