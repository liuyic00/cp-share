From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import StatementFacts ScalarEvaluation.
From SmallMultiplier Require Import Model NodeCertificateCheck Child2Stable Child2Local.
Local Open Scope N_scope.
Lemma node_12_certificate : node_certificate 12 expr_word_12 generated_module_2_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_12 invalid v old before after
 (H0 : VM.find 2 old = Some (Gval (Fuint 1) (word_2 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 VM.find 12 after = Some (Gval (Fuint 4) (word_12 v)).
Proof. eapply pass_node_value; [exact node_12_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_12_value; assumption. Qed.
Lemma node_13_certificate : node_certificate 13 expr_word_13 generated_module_2_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_13 invalid v old before after
 (H0 : VM.find 3 old = Some (Gval (Fuint 1) (word_3 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 VM.find 13 after = Some (Gval (Fuint 4) (word_13 v)).
Proof. eapply pass_node_value; [exact node_13_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_13_value; assumption. Qed.
Lemma node_14_certificate : node_certificate 14 expr_word_14 generated_module_2_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_14 invalid v old before after
 (H0 : VM.find 4 old = Some (Gval (Fuint 1) (word_4 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 VM.find 14 after = Some (Gval (Fuint 4) (word_14 v)).
Proof. eapply pass_node_value; [exact node_14_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_14_value; assumption. Qed.
Lemma node_15_certificate : node_certificate 15 expr_word_15 generated_module_2_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_15 invalid v old before after
 (H0 : VM.find 5 old = Some (Gval (Fuint 1) (word_5 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 VM.find 15 after = Some (Gval (Fuint 4) (word_15 v)).
Proof. eapply pass_node_value; [exact node_15_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_15_value; assumption. Qed.
Lemma node_16_certificate : node_certificate 16 expr_word_16 generated_module_2_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_16 invalid v old before after
 (H0 : VM.find 6 old = Some (Gval (Fuint 1) (word_6 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 VM.find 16 after = Some (Gval (Fuint 4) (word_16 v)).
Proof. eapply pass_node_value; [exact node_16_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_16_value; assumption. Qed.
Lemma node_17_certificate : node_certificate 17 expr_word_17 generated_module_2_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_17 invalid v old before after
 (H0 : VM.find 12 old = Some (Gval (Fuint 4) (word_12 v)))
 (H1 : VM.find 13 old = Some (Gval (Fuint 4) (word_13 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 VM.find 17 after = Some (Gval (Fuint 5) (word_17 v)).
Proof. eapply pass_node_value; [exact node_17_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_17_value; assumption. Qed.
Lemma node_18_certificate : node_certificate 18 expr_word_18 generated_module_2_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_18 invalid v old before after
 (H0 : VM.find 17 old = Some (Gval (Fuint 5) (word_17 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 VM.find 18 after = Some (Gval (Fuint 4) (word_18 v)).
Proof. eapply pass_node_value; [exact node_18_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_18_value; assumption. Qed.
Lemma node_19_certificate : node_certificate 19 expr_word_19 generated_module_2_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_19 invalid v old before after
 (H0 : VM.find 14 old = Some (Gval (Fuint 4) (word_14 v)))
 (H1 : VM.find 18 old = Some (Gval (Fuint 4) (word_18 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 VM.find 19 after = Some (Gval (Fuint 5) (word_19 v)).
Proof. eapply pass_node_value; [exact node_19_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_19_value; assumption. Qed.
Lemma node_20_certificate : node_certificate 20 expr_word_20 generated_module_2_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_20 invalid v old before after
 (H0 : VM.find 19 old = Some (Gval (Fuint 5) (word_19 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 VM.find 20 after = Some (Gval (Fuint 4) (word_20 v)).
Proof. eapply pass_node_value; [exact node_20_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_20_value; assumption. Qed.
Lemma node_21_certificate : node_certificate 21 expr_word_21 generated_module_2_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_21 invalid v old before after
 (H0 : VM.find 15 old = Some (Gval (Fuint 4) (word_15 v)))
 (H1 : VM.find 20 old = Some (Gval (Fuint 4) (word_20 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 VM.find 21 after = Some (Gval (Fuint 5) (word_21 v)).
Proof. eapply pass_node_value; [exact node_21_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_21_value; assumption. Qed.
Lemma node_22_certificate : node_certificate 22 expr_word_22 generated_module_2_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_22 invalid v old before after
 (H0 : VM.find 21 old = Some (Gval (Fuint 5) (word_21 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 VM.find 22 after = Some (Gval (Fuint 4) (word_22 v)).
Proof. eapply pass_node_value; [exact node_22_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_22_value; assumption. Qed.
Lemma node_23_certificate : node_certificate 23 expr_word_23 generated_module_2_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_23 invalid v old before after
 (H0 : VM.find 16 old = Some (Gval (Fuint 4) (word_16 v)))
 (H1 : VM.find 22 old = Some (Gval (Fuint 4) (word_22 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 VM.find 23 after = Some (Gval (Fuint 5) (word_23 v)).
Proof. eapply pass_node_value; [exact node_23_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_23_value; assumption. Qed.
Lemma node_24_certificate : node_certificate 24 expr_word_24 generated_module_2_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_24 invalid v old before after
 (H0 : VM.find 23 old = Some (Gval (Fuint 5) (word_23 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 VM.find 24 after = Some (Gval (Fuint 4) (word_24 v)).
Proof. eapply pass_node_value; [exact node_24_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_24_value; assumption. Qed.
Lemma node_25_certificate : node_certificate 25 expr_word_25 generated_module_2_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_25 invalid v old before after
 (H0 : VM.find 7 old = Some (Gval (Fuint 1) (word_7 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 VM.find 25 after = Some (Gval (Fuint 4) (word_25 v)).
Proof. eapply pass_node_value; [exact node_25_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_25_value; assumption. Qed.
Lemma node_26_certificate : node_certificate 26 expr_word_26 generated_module_2_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_26 invalid v old before after
 (H0 : VM.find 8 old = Some (Gval (Fuint 1) (word_8 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 VM.find 26 after = Some (Gval (Fuint 4) (word_26 v)).
Proof. eapply pass_node_value; [exact node_26_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_26_value; assumption. Qed.
Lemma node_27_certificate : node_certificate 27 expr_word_27 generated_module_2_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_27 invalid v old before after
 (H0 : VM.find 26 old = Some (Gval (Fuint 4) (word_26 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 VM.find 27 after = Some (Gval (Fuint 5) (word_27 v)).
Proof. eapply pass_node_value; [exact node_27_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_27_value; assumption. Qed.
Lemma node_28_certificate : node_certificate 28 expr_word_28 generated_module_2_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_28 invalid v old before after
 (H0 : VM.find 9 old = Some (Gval (Fuint 1) (word_9 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 VM.find 28 after = Some (Gval (Fuint 4) (word_28 v)).
Proof. eapply pass_node_value; [exact node_28_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_28_value; assumption. Qed.
Lemma node_29_certificate : node_certificate 29 expr_word_29 generated_module_2_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_29 invalid v old before after
 (H0 : VM.find 28 old = Some (Gval (Fuint 4) (word_28 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 VM.find 29 after = Some (Gval (Fuint 5) (word_29 v)).
Proof. eapply pass_node_value; [exact node_29_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_29_value; assumption. Qed.
Lemma node_30_certificate : node_certificate 30 expr_word_30 generated_module_2_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_30 invalid v old before after
 (H0 : VM.find 25 old = Some (Gval (Fuint 4) (word_25 v)))
 (H1 : VM.find 27 old = Some (Gval (Fuint 5) (word_27 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 VM.find 30 after = Some (Gval (Fuint 6) (word_30 v)).
Proof. eapply pass_node_value; [exact node_30_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_30_value; assumption. Qed.
Lemma node_31_certificate : node_certificate 31 expr_word_31 generated_module_2_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_31 invalid v old before after
 (H0 : VM.find 30 old = Some (Gval (Fuint 6) (word_30 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 VM.find 31 after = Some (Gval (Fuint 5) (word_31 v)).
Proof. eapply pass_node_value; [exact node_31_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_31_value; assumption. Qed.
Lemma node_32_certificate : node_certificate 32 expr_word_32 generated_module_2_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_32 invalid v old before after
 (H0 : VM.find 29 old = Some (Gval (Fuint 5) (word_29 v)))
 (H1 : VM.find 31 old = Some (Gval (Fuint 5) (word_31 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 VM.find 32 after = Some (Gval (Fuint 6) (word_32 v)).
Proof. eapply pass_node_value; [exact node_32_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_32_value; assumption. Qed.
Lemma node_33_certificate : node_certificate 33 expr_word_33 generated_module_2_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_33 invalid v old before after
 (H0 : VM.find 32 old = Some (Gval (Fuint 6) (word_32 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 VM.find 33 after = Some (Gval (Fuint 5) (word_33 v)).
Proof. eapply pass_node_value; [exact node_33_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_33_value; assumption. Qed.
Lemma node_34_certificate : node_certificate 34 expr_word_34 generated_module_2_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_34 invalid v old before after
 (H0 : VM.find 24 old = Some (Gval (Fuint 4) (word_24 v)))
 (H1 : VM.find 33 old = Some (Gval (Fuint 5) (word_33 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 VM.find 34 after = Some (Gval (Fuint 1) (word_34 v)).
Proof. eapply pass_node_value; [exact node_34_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_34_value; assumption. Qed.
Lemma node_35_certificate : node_certificate 35 expr_word_35 generated_module_2_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_35 invalid v old before after
 (H0 : VM.find 1 old = Some (Gval (Fuint 1) (word_1 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 VM.find 35 after = Some (Gval (Fuint 1) (word_35 v)).
Proof. eapply pass_node_value; [exact node_35_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_35_value; assumption. Qed.
Lemma node_36_certificate : node_certificate 36 expr_word_36 generated_module_2_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_36 invalid v old before after
 (H0 : VM.find 35 old = Some (Gval (Fuint 1) (word_35 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 VM.find 36 after = Some (Gval (Fuint 1) (word_36 v)).
Proof. eapply pass_node_value; [exact node_36_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_36_value; assumption. Qed.
Lemma node_37_certificate : node_certificate 37 expr_word_37 generated_module_2_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_37 invalid v old before after
 (H0 : VM.find 34 old = Some (Gval (Fuint 1) (word_34 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 VM.find 37 after = Some (Gval (Fuint 1) (word_37 v)).
Proof. eapply pass_node_value; [exact node_37_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_37_value; assumption. Qed.
Lemma node_38_certificate : node_certificate 38 expr_word_38 generated_module_2_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_38 invalid v old before after
 (H0 : eval_href (@Esubfield VarOrder.T (@Eid VarOrder.T 10) 5) old old = Some (Gval (Fuint 1) (port_10_5 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 VM.find 38 after = Some (Gval (Fuint 1) (word_38 v)).
Proof. eapply pass_node_value; [exact node_38_certificate|vm_compute;reflexivity| |exact ran].
 change (eval_hfexpr expr_word_38 old old = Some (Gval (Fuint 1) (word_38 v))).
 apply local_word_38_value; assumption. Qed.
Lemma node_39_certificate : node_certificate 39 expr_word_39 generated_module_2_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_39 invalid v old before after
 (H0 : VM.find 5 old = Some (Gval (Fuint 1) (word_5 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 VM.find 39 after = Some (Gval (Fuint 1) (word_39 v)).
Proof. eapply pass_node_value; [exact node_39_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_39_value; assumption. Qed.
Lemma node_40_certificate : node_certificate 40 expr_word_40 generated_module_2_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_40 invalid v old before after
 (H0 : VM.find 6 old = Some (Gval (Fuint 1) (word_6 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 VM.find 40 after = Some (Gval (Fuint 1) (word_40 v)).
Proof. eapply pass_node_value; [exact node_40_certificate|vm_compute;reflexivity| |exact ran].
 rewrite scalar_eval_memory_irrelevant; [|reflexivity].
 apply local_word_40_value; assumption. Qed.
Lemma node_41_certificate : node_certificate 41 expr_word_41 generated_module_2_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_41 invalid v old before after
 (H0 : eval_href (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 5) old old = Some (Gval (Fuint 1) (port_11_5 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 VM.find 41 after = Some (Gval (Fuint 1) (word_41 v)).
Proof. eapply pass_node_value; [exact node_41_certificate|vm_compute;reflexivity| |exact ran].
 change (eval_hfexpr expr_word_41 old old = Some (Gval (Fuint 1) (word_41 v))).
 apply local_word_41_value; assumption. Qed.
Lemma node_42_certificate : node_certificate 42 expr_word_42 generated_module_2_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_42 invalid v old before after
 (H0 : eval_href (@Esubfield VarOrder.T (@Eid VarOrder.T 10) 6) old old = Some (Gval (Fuint 1) (port_10_6 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 VM.find 42 after = Some (Gval (Fuint 1) (word_42 v)).
Proof. eapply pass_node_value; [exact node_42_certificate|vm_compute;reflexivity| |exact ran].
 change (eval_hfexpr expr_word_42 old old = Some (Gval (Fuint 1) (word_42 v))).
 apply local_word_42_value; assumption. Qed.
Lemma node_43_certificate : node_certificate 43 expr_word_43 generated_module_2_stmts_0.
Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.
Lemma pass_word_43 invalid v old before after
 (H0 : eval_href (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 6) old old = Some (Gval (Fuint 1) (port_11_6 v)))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 VM.find 43 after = Some (Gval (Fuint 1) (word_43 v)).
Proof. eapply pass_node_value; [exact node_43_certificate|vm_compute;reflexivity| |exact ran].
 change (eval_hfexpr expr_word_43 old old = Some (Gval (Fuint 1) (word_43 v))).
 apply local_word_43_value; assumption. Qed.
