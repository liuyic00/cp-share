From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import StatementFacts ConnectionFacts GroundFrames ScalarEvaluation
 ScalarExtensionality RankConvergence InstanceFoldFacts.
From Divider Require Import Model Stable Typing Certificates Frames SingleModule.
Local Open Scope N_scope.
From Divider Require Import NodeProgress.
Section Progress.
Variable v : leaf_values.
Hypothesis leaf_0_size : size (v 0) = 1%nat.
Hypothesis leaf_1_size : size (v 1) = 1%nat.
Hypothesis leaf_3_size : size (v 3) = 1%nat.
Hypothesis leaf_4_size : size (v 4) = 64%nat.
Hypothesis leaf_5_size : size (v 5) = 64%nat.
Hypothesis leaf_6_size : size (v 6) = 64%nat.
Hypothesis leaf_7_size : size (v 7) = 1%nat.
Hypothesis leaf_10_size : size (v 10) = 1%nat.
Hypothesis leaf_11_size : size (v 11) = 1%nat.
Hypothesis leaf_12_size : size (v 12) = 1%nat.
Hypothesis leaf_13_size : size (v 13) = 3%nat.
Hypothesis leaf_18_size : size (v 18) = 1%nat.
Hypothesis leaf_20_size : size (v 20) = 129%nat.
Hypothesis leaf_33_size : size (v 33) = 1%nat.
Hypothesis leaf_38_size : size (v 38) = 1%nat.
Hypothesis leaf_40_size : size (v 40) = 64%nat.
Hypothesis leaf_43_size : size (v 43) = 65%nat.
Hypothesis leaf_45_size : size (v 45) = 1%nat.
Hypothesis leaf_46_size : size (v 46) = 1%nat.
Hypothesis leaf_47_size : size (v 47) = 1%nat.
Hypothesis leaf_51_size : size (v 51) = 6%nat.
Hypothesis leaf_445_size : size (v 445) = 1%nat.
Hypothesis leaf_446_size : size (v 446) = 3%nat.
Hypothesis leaf_447_size : size (v 447) = 6%nat.
Hypothesis leaf_475_size : size (v 475) = 1%nat.
Hypothesis leaf_476_size : size (v 476) = 64%nat.
Lemma pass_output_2_type invalid old before after value
 (found : VM.find 2 before = Some value) (typed : type_of_val value = Gtyp (Fuint 1))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_0_stmts_0 = Some after) :
 exists result, VM.find 2 after = Some result /\ type_of_val result = Gtyp (Fuint 1).
Proof.
 eapply pass_framed_write_ground_type; [exact output_2_certificate|exact output_2_not_register|exact typed|exact found| |exact ran].
 intros position initial final initial_value lookup initial_type step.
 eapply bidirectional_eid_preserves_target_type with (source:=420) (target:=2) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| |].
 - cbn [eval_type_of_ref]. rewrite lookup. cbn [option_map]. rewrite initial_type. reflexivity.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Lemma pass_output_2 invalid n old before after value
 (agree : rank_agrees_on divider_domain dependency_rank (stable_env v) n old)
 (bound : Nat.le (dependency_rank 2) (S n))
 (found : VM.find 2 before = Some value) (typed : type_of_val value = Gtyp (Fuint 1))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_0_stmts_0 = Some after) :
 VM.find 2 after = VM.find 2 (stable_env v).
Proof.
 have source_eq : VM.find 420 old = VM.find 420 (stable_env v).
 { apply agree; [unfold divider_domain; vm_compute; reflexivity|].
    have smaller : Nat.lt (dependency_rank 420) (dependency_rank 2) by vm_compute; repeat constructor.
    lia. }
 rewrite (target_2_value v).
 eapply pass_framed_write_value; [exact output_2_certificate|exact output_2_not_register|exact typed|exact found| |exact ran].
 intros position initial final lookup step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (word_420 v)) (source:=420) (target:=2) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | | |].
 - cbn [eval_type_of_ref]. rewrite lookup. cbn [option_map]. rewrite typed. reflexivity.
 - change (VM.find 420 old = Some (Gval (Fuint 1) (word_420 v))).
   rewrite source_eq. exact (target_420_value v).
 - have size_source : size (word_420 v) = 1%nat by (apply word_420_size; assumption).
   change (Some (Gval (Fuint 1) (zext_to 1 (take 1 (word_420 v)))) = Some (Gval (Fuint 1) (word_2 v))).
   have trim : zext_to 1 (take 1 (word_420 v)) = word_420 v.
   { rewrite -size_source take_size /zext_to subnn zext0. reflexivity. }
   rewrite trim.
   change (Some (Gval (Fuint 1) (word_420 v)) = Some (Gval (Fuint 1) (word_2 v))).
   have same := node_2_value v.
   change (VM.find 420 (stable_env v) = Some (Gval (Fuint 1) (word_2 v))) in same.
   rewrite (target_420_value v) in same. exact same.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Lemma pass_output_8_type invalid old before after value
 (found : VM.find 8 before = Some value) (typed : type_of_val value = Gtyp (Fuint 1))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_0_stmts_0 = Some after) :
 exists result, VM.find 8 after = Some result /\ type_of_val result = Gtyp (Fuint 1).
Proof.
 eapply pass_framed_write_ground_type; [exact output_8_certificate|exact output_8_not_register|exact typed|exact found| |exact ran].
 intros position initial final initial_value lookup initial_type step.
 eapply bidirectional_eid_preserves_target_type with (source:=419) (target:=8) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| |].
 - cbn [eval_type_of_ref]. rewrite lookup. cbn [option_map]. rewrite initial_type. reflexivity.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Lemma pass_output_8 invalid n old before after value
 (agree : rank_agrees_on divider_domain dependency_rank (stable_env v) n old)
 (bound : Nat.le (dependency_rank 8) (S n))
 (found : VM.find 8 before = Some value) (typed : type_of_val value = Gtyp (Fuint 1))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_0_stmts_0 = Some after) :
 VM.find 8 after = VM.find 8 (stable_env v).
Proof.
 have source_eq : VM.find 419 old = VM.find 419 (stable_env v).
 { apply agree; [unfold divider_domain; vm_compute; reflexivity|].
    have smaller : Nat.lt (dependency_rank 419) (dependency_rank 8) by vm_compute; repeat constructor.
    lia. }
 rewrite (target_8_value v).
 eapply pass_framed_write_value; [exact output_8_certificate|exact output_8_not_register|exact typed|exact found| |exact ran].
 intros position initial final lookup step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (word_419 v)) (source:=419) (target:=8) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | | |].
 - cbn [eval_type_of_ref]. rewrite lookup. cbn [option_map]. rewrite typed. reflexivity.
 - change (VM.find 419 old = Some (Gval (Fuint 1) (word_419 v))).
   rewrite source_eq. exact (target_419_value v).
 - have size_source : size (word_419 v) = 1%nat by (apply word_419_size; assumption).
   change (Some (Gval (Fuint 1) (zext_to 1 (take 1 (word_419 v)))) = Some (Gval (Fuint 1) (word_8 v))).
   have trim : zext_to 1 (take 1 (word_419 v)) = word_419 v.
   { rewrite -size_source take_size /zext_to subnn zext0. reflexivity. }
   rewrite trim.
   change (Some (Gval (Fuint 1) (word_419 v)) = Some (Gval (Fuint 1) (word_8 v))).
   have same := node_8_value v.
   change (VM.find 419 (stable_env v) = Some (Gval (Fuint 1) (word_8 v))) in same.
   rewrite (target_419_value v) in same. exact same.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Lemma pass_output_9_type invalid old before after value
 (found : VM.find 9 before = Some value) (typed : type_of_val value = Gtyp (Fuint 64))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_0_stmts_0 = Some after) :
 exists result, VM.find 9 after = Some result /\ type_of_val result = Gtyp (Fuint 64).
Proof.
 eapply pass_framed_write_ground_type; [exact output_9_certificate|exact output_9_not_register|exact typed|exact found| |exact ran].
 intros position initial final initial_value lookup initial_type step.
 eapply bidirectional_eid_preserves_target_type with (source:=418) (target:=9) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| |].
 - cbn [eval_type_of_ref]. rewrite lookup. cbn [option_map]. rewrite initial_type. reflexivity.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Lemma pass_output_9 invalid n old before after value
 (agree : rank_agrees_on divider_domain dependency_rank (stable_env v) n old)
 (bound : Nat.le (dependency_rank 9) (S n))
 (found : VM.find 9 before = Some value) (typed : type_of_val value = Gtyp (Fuint 64))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_0_stmts_0 = Some after) :
 VM.find 9 after = VM.find 9 (stable_env v).
Proof.
 have source_eq : VM.find 418 old = VM.find 418 (stable_env v).
 { apply agree; [unfold divider_domain; vm_compute; reflexivity|].
    have smaller : Nat.lt (dependency_rank 418) (dependency_rank 9) by vm_compute; repeat constructor.
    lia. }
 rewrite (target_9_value v).
 eapply pass_framed_write_value; [exact output_9_certificate|exact output_9_not_register|exact typed|exact found| |exact ran].
 intros position initial final lookup step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 64) (word_418 v)) (source:=418) (target:=9) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | | |].
 - cbn [eval_type_of_ref]. rewrite lookup. cbn [option_map]. rewrite typed. reflexivity.
 - change (VM.find 418 old = Some (Gval (Fuint 64) (word_418 v))).
   rewrite source_eq. exact (target_418_value v).
 - have size_source : size (word_418 v) = 64%nat by (apply word_418_size; assumption).
   change (Some (Gval (Fuint 64) (zext_to 64 (take 64 (word_418 v)))) = Some (Gval (Fuint 64) (word_9 v))).
   have trim : zext_to 64 (take 64 (word_418 v)) = word_418 v.
   { rewrite -size_source take_size /zext_to subnn zext0. reflexivity. }
   rewrite trim.
   change (Some (Gval (Fuint 64) (word_418 v)) = Some (Gval (Fuint 64) (word_9 v))).
   have same := node_9_value v.
   change (VM.find 418 (stable_env v) = Some (Gval (Fuint 64) (word_9 v))) in same.
   rewrite (target_418_value v) in same. exact same.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Lemma pass_leaf_0 invalid n old after
 (agree : rank_agrees_on divider_domain dependency_rank (stable_env v) n old)
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false old generated_module_0_stmts_0 = Some after) :
 VM.find 0 after = VM.find 0 (stable_env v).
Proof.
 have known : VM.find 0 old = Some (Gval Fclock (word_0 v)).
 { rewrite -(target_0_value v). apply agree; [unfold divider_domain; vm_compute; reflexivity|change (Nat.le O n); lia]. }
 rewrite (target_0_value v).
 eapply pass_preserves_ground; [exact input_0_frame|exact input_0_not_register|reflexivity|exact known|exact ran].
Qed.
Lemma pass_leaf_1 invalid n old after
 (agree : rank_agrees_on divider_domain dependency_rank (stable_env v) n old)
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false old generated_module_0_stmts_0 = Some after) :
 VM.find 1 after = VM.find 1 (stable_env v).
Proof.
 have known : VM.find 1 old = Some (Gval (Fuint 1) (word_1 v)).
 { rewrite -(target_1_value v). apply agree; [unfold divider_domain; vm_compute; reflexivity|change (Nat.le O n); lia]. }
 rewrite (target_1_value v).
 eapply pass_preserves_ground; [exact input_1_frame|exact input_1_not_register|reflexivity|exact known|exact ran].
Qed.
Lemma pass_leaf_3 invalid n old after
 (agree : rank_agrees_on divider_domain dependency_rank (stable_env v) n old)
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false old generated_module_0_stmts_0 = Some after) :
 VM.find 3 after = VM.find 3 (stable_env v).
Proof.
 have known : VM.find 3 old = Some (Gval (Fuint 1) (word_3 v)).
 { rewrite -(target_3_value v). apply agree; [unfold divider_domain; vm_compute; reflexivity|change (Nat.le O n); lia]. }
 rewrite (target_3_value v).
 eapply pass_preserves_ground; [exact input_3_frame|exact input_3_not_register|reflexivity|exact known|exact ran].
Qed.
Lemma pass_leaf_4 invalid n old after
 (agree : rank_agrees_on divider_domain dependency_rank (stable_env v) n old)
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false old generated_module_0_stmts_0 = Some after) :
 VM.find 4 after = VM.find 4 (stable_env v).
Proof.
 have known : VM.find 4 old = Some (Gval (Fuint 64) (word_4 v)).
 { rewrite -(target_4_value v). apply agree; [unfold divider_domain; vm_compute; reflexivity|change (Nat.le O n); lia]. }
 rewrite (target_4_value v).
 eapply pass_preserves_ground; [exact input_4_frame|exact input_4_not_register|reflexivity|exact known|exact ran].
Qed.
Lemma pass_leaf_5 invalid n old after
 (agree : rank_agrees_on divider_domain dependency_rank (stable_env v) n old)
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false old generated_module_0_stmts_0 = Some after) :
 VM.find 5 after = VM.find 5 (stable_env v).
Proof.
 have known : VM.find 5 old = Some (Gval (Fuint 64) (word_5 v)).
 { rewrite -(target_5_value v). apply agree; [unfold divider_domain; vm_compute; reflexivity|change (Nat.le O n); lia]. }
 rewrite (target_5_value v).
 eapply pass_preserves_ground; [exact input_5_frame|exact input_5_not_register|reflexivity|exact known|exact ran].
Qed.
Lemma pass_leaf_6 invalid n old after
 (agree : rank_agrees_on divider_domain dependency_rank (stable_env v) n old)
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false old generated_module_0_stmts_0 = Some after) :
 VM.find 6 after = VM.find 6 (stable_env v).
Proof.
 have known : VM.find 6 old = Some (Gval (Fuint 64) (word_6 v)).
 { rewrite -(target_6_value v). apply agree; [unfold divider_domain; vm_compute; reflexivity|change (Nat.le O n); lia]. }
 rewrite (target_6_value v).
 eapply pass_preserves_ground; [exact input_6_frame|exact input_6_not_register|reflexivity|exact known|exact ran].
Qed.
Lemma pass_leaf_7 invalid n old after
 (agree : rank_agrees_on divider_domain dependency_rank (stable_env v) n old)
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false old generated_module_0_stmts_0 = Some after) :
 VM.find 7 after = VM.find 7 (stable_env v).
Proof.
 have known : VM.find 7 old = Some (Gval (Fuint 1) (word_7 v)).
 { rewrite -(target_7_value v). apply agree; [unfold divider_domain; vm_compute; reflexivity|change (Nat.le O n); lia]. }
 rewrite (target_7_value v).
 eapply pass_preserves_ground; [exact input_7_frame|exact input_7_not_register|reflexivity|exact known|exact ran].
Qed.
Lemma pass_leaf_10 invalid n old after
 (agree : rank_agrees_on divider_domain dependency_rank (stable_env v) n old)
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false old generated_module_0_stmts_0 = Some after) :
 VM.find 10 after = VM.find 10 (stable_env v).
Proof.
 have known : VM.find 10 old = Some (Gval (Fuint 1) (word_10 v)).
 { rewrite -(target_10_value v). apply agree; [unfold divider_domain; vm_compute; reflexivity|change (Nat.le O n); lia]. }
 rewrite (target_10_value v).
 eapply pass_preserves_ground; [exact input_10_frame|exact input_10_not_register|reflexivity|exact known|exact ran].
Qed.
Lemma pass_leaf_11 invalid n old after
 (agree : rank_agrees_on divider_domain dependency_rank (stable_env v) n old)
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false old generated_module_0_stmts_0 = Some after) :
 VM.find 11 after = VM.find 11 (stable_env v).
Proof.
 have known : VM.find 11 old = Some (Gval (Fuint 1) (word_11 v)).
 { rewrite -(target_11_value v). apply agree; [unfold divider_domain; vm_compute; reflexivity|change (Nat.le O n); lia]. }
 rewrite (target_11_value v).
 eapply pass_preserves_ground; [exact input_11_frame|exact input_11_not_register|reflexivity|exact known|exact ran].
Qed.
Lemma pass_leaf_12 invalid n old after
 (agree : rank_agrees_on divider_domain dependency_rank (stable_env v) n old)
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false old generated_module_0_stmts_0 = Some after) :
 VM.find 12 after = VM.find 12 (stable_env v).
Proof.
 have known : VM.find 12 old = Some (Gval (Fuint 1) (word_12 v)).
 { rewrite -(target_12_value v). apply agree; [unfold divider_domain; vm_compute; reflexivity|change (Nat.le O n); lia]. }
 rewrite (target_12_value v).
 eapply pass_preserves_ground; [exact input_12_frame|exact input_12_not_register|reflexivity|exact known|exact ran].
Qed.
Lemma pass_leaf_13 invalid n old after
 (agree : rank_agrees_on divider_domain dependency_rank (stable_env v) n old)
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false old generated_module_0_stmts_0 = Some after) :
 VM.find 13 after = VM.find 13 (stable_env v).
Proof.
 have known : VM.find 13 old = Some (Gval (Fuint 3) (word_13 v)).
 { rewrite -(target_13_value v). apply agree; [unfold divider_domain; vm_compute; reflexivity|change (Nat.le O n); lia]. }
 rewrite (target_13_value v).
 eapply pass_register_preserved; [exact known|exact register_13_certificate|exact ran].
Qed.
Lemma pass_leaf_18 invalid n old after
 (agree : rank_agrees_on divider_domain dependency_rank (stable_env v) n old)
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false old generated_module_0_stmts_0 = Some after) :
 VM.find 18 after = VM.find 18 (stable_env v).
Proof.
 have known : VM.find 18 old = Some (Gval (Fuint 1) (word_18 v)).
 { rewrite -(target_18_value v). apply agree; [unfold divider_domain; vm_compute; reflexivity|change (Nat.le O n); lia]. }
 rewrite (target_18_value v).
 eapply pass_register_preserved; [exact known|exact register_18_certificate|exact ran].
Qed.
Lemma pass_leaf_20 invalid n old after
 (agree : rank_agrees_on divider_domain dependency_rank (stable_env v) n old)
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false old generated_module_0_stmts_0 = Some after) :
 VM.find 20 after = VM.find 20 (stable_env v).
Proof.
 have known : VM.find 20 old = Some (Gval (Fuint 129) (word_20 v)).
 { rewrite -(target_20_value v). apply agree; [unfold divider_domain; vm_compute; reflexivity|change (Nat.le O n); lia]. }
 rewrite (target_20_value v).
 eapply pass_register_preserved; [exact known|exact register_20_certificate|exact ran].
Qed.
Lemma pass_leaf_33 invalid n old after
 (agree : rank_agrees_on divider_domain dependency_rank (stable_env v) n old)
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false old generated_module_0_stmts_0 = Some after) :
 VM.find 33 after = VM.find 33 (stable_env v).
Proof.
 have known : VM.find 33 old = Some (Gval (Fuint 1) (word_33 v)).
 { rewrite -(target_33_value v). apply agree; [unfold divider_domain; vm_compute; reflexivity|change (Nat.le O n); lia]. }
 rewrite (target_33_value v).
 eapply pass_register_preserved; [exact known|exact register_33_certificate|exact ran].
Qed.
Lemma pass_leaf_38 invalid n old after
 (agree : rank_agrees_on divider_domain dependency_rank (stable_env v) n old)
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false old generated_module_0_stmts_0 = Some after) :
 VM.find 38 after = VM.find 38 (stable_env v).
Proof.
 have known : VM.find 38 old = Some (Gval (Fuint 1) (word_38 v)).
 { rewrite -(target_38_value v). apply agree; [unfold divider_domain; vm_compute; reflexivity|change (Nat.le O n); lia]. }
 rewrite (target_38_value v).
 eapply pass_register_preserved; [exact known|exact register_38_certificate|exact ran].
Qed.
Lemma pass_leaf_40 invalid n old after
 (agree : rank_agrees_on divider_domain dependency_rank (stable_env v) n old)
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false old generated_module_0_stmts_0 = Some after) :
 VM.find 40 after = VM.find 40 (stable_env v).
Proof.
 have known : VM.find 40 old = Some (Gval (Fuint 64) (word_40 v)).
 { rewrite -(target_40_value v). apply agree; [unfold divider_domain; vm_compute; reflexivity|change (Nat.le O n); lia]. }
 rewrite (target_40_value v).
 eapply pass_register_preserved; [exact known|exact register_40_certificate|exact ran].
Qed.
Lemma pass_leaf_43 invalid n old after
 (agree : rank_agrees_on divider_domain dependency_rank (stable_env v) n old)
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false old generated_module_0_stmts_0 = Some after) :
 VM.find 43 after = VM.find 43 (stable_env v).
Proof.
 have known : VM.find 43 old = Some (Gval (Fuint 65) (word_43 v)).
 { rewrite -(target_43_value v). apply agree; [unfold divider_domain; vm_compute; reflexivity|change (Nat.le O n); lia]. }
 rewrite (target_43_value v).
 eapply pass_register_preserved; [exact known|exact register_43_certificate|exact ran].
Qed.
Lemma pass_leaf_45 invalid n old after
 (agree : rank_agrees_on divider_domain dependency_rank (stable_env v) n old)
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false old generated_module_0_stmts_0 = Some after) :
 VM.find 45 after = VM.find 45 (stable_env v).
Proof.
 have known : VM.find 45 old = Some (Gval (Fuint 1) (word_45 v)).
 { rewrite -(target_45_value v). apply agree; [unfold divider_domain; vm_compute; reflexivity|change (Nat.le O n); lia]. }
 rewrite (target_45_value v).
 eapply pass_register_preserved; [exact known|exact register_45_certificate|exact ran].
Qed.
Lemma pass_leaf_46 invalid n old after
 (agree : rank_agrees_on divider_domain dependency_rank (stable_env v) n old)
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false old generated_module_0_stmts_0 = Some after) :
 VM.find 46 after = VM.find 46 (stable_env v).
Proof.
 have known : VM.find 46 old = Some (Gval (Fuint 1) (word_46 v)).
 { rewrite -(target_46_value v). apply agree; [unfold divider_domain; vm_compute; reflexivity|change (Nat.le O n); lia]. }
 rewrite (target_46_value v).
 eapply pass_register_preserved; [exact known|exact register_46_certificate|exact ran].
Qed.
Lemma pass_leaf_47 invalid n old after
 (agree : rank_agrees_on divider_domain dependency_rank (stable_env v) n old)
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false old generated_module_0_stmts_0 = Some after) :
 VM.find 47 after = VM.find 47 (stable_env v).
Proof.
 have known : VM.find 47 old = Some (Gval (Fuint 1) (word_47 v)).
 { rewrite -(target_47_value v). apply agree; [unfold divider_domain; vm_compute; reflexivity|change (Nat.le O n); lia]. }
 rewrite (target_47_value v).
 eapply pass_register_preserved; [exact known|exact register_47_certificate|exact ran].
Qed.
Lemma pass_leaf_51 invalid n old after
 (agree : rank_agrees_on divider_domain dependency_rank (stable_env v) n old)
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false old generated_module_0_stmts_0 = Some after) :
 VM.find 51 after = VM.find 51 (stable_env v).
Proof.
 have known : VM.find 51 old = Some (Gval (Fuint 6) (word_51 v)).
 { rewrite -(target_51_value v). apply agree; [unfold divider_domain; vm_compute; reflexivity|change (Nat.le O n); lia]. }
 rewrite (target_51_value v).
 eapply pass_register_preserved; [exact known|exact register_51_certificate|exact ran].
Qed.
Lemma pass_leaf_445 invalid n old after
 (agree : rank_agrees_on divider_domain dependency_rank (stable_env v) n old)
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false old generated_module_0_stmts_0 = Some after) :
 VM.find 445 after = VM.find 445 (stable_env v).
Proof.
 have known : VM.find 445 old = Some (Gval (Fuint 1) (word_445 v)).
 { rewrite -(target_445_value v). apply agree; [unfold divider_domain; vm_compute; reflexivity|change (Nat.le O n); lia]. }
 rewrite (target_445_value v).
 eapply pass_register_preserved; [exact known|exact register_445_certificate|exact ran].
Qed.
Lemma pass_leaf_446 invalid n old after
 (agree : rank_agrees_on divider_domain dependency_rank (stable_env v) n old)
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false old generated_module_0_stmts_0 = Some after) :
 VM.find 446 after = VM.find 446 (stable_env v).
Proof.
 have known : VM.find 446 old = Some (Gval (Fuint 3) (word_446 v)).
 { rewrite -(target_446_value v). apply agree; [unfold divider_domain; vm_compute; reflexivity|change (Nat.le O n); lia]. }
 rewrite (target_446_value v).
 eapply pass_register_preserved; [exact known|exact register_446_certificate|exact ran].
Qed.
Lemma pass_leaf_447 invalid n old after
 (agree : rank_agrees_on divider_domain dependency_rank (stable_env v) n old)
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false old generated_module_0_stmts_0 = Some after) :
 VM.find 447 after = VM.find 447 (stable_env v).
Proof.
 have known : VM.find 447 old = Some (Gval (Fuint 6) (word_447 v)).
 { rewrite -(target_447_value v). apply agree; [unfold divider_domain; vm_compute; reflexivity|change (Nat.le O n); lia]. }
 rewrite (target_447_value v).
 eapply pass_register_preserved; [exact known|exact register_447_certificate|exact ran].
Qed.
Lemma pass_leaf_475 invalid n old after
 (agree : rank_agrees_on divider_domain dependency_rank (stable_env v) n old)
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false old generated_module_0_stmts_0 = Some after) :
 VM.find 475 after = VM.find 475 (stable_env v).
Proof.
 have known : VM.find 475 old = Some (Gval (Fuint 1) (word_475 v)).
 { rewrite -(target_475_value v). apply agree; [unfold divider_domain; vm_compute; reflexivity|change (Nat.le O n); lia]. }
 rewrite (target_475_value v).
 eapply pass_register_preserved; [exact known|exact register_475_certificate|exact ran].
Qed.
Lemma pass_leaf_476 invalid n old after
 (agree : rank_agrees_on divider_domain dependency_rank (stable_env v) n old)
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false old generated_module_0_stmts_0 = Some after) :
 VM.find 476 after = VM.find 476 (stable_env v).
Proof.
 have known : VM.find 476 old = Some (Gval (Fuint 64) (word_476 v)).
 { rewrite -(target_476_value v). apply agree; [unfold divider_domain; vm_compute; reflexivity|change (Nat.le O n); lia]. }
 rewrite (target_476_value v).
 eapply pass_register_preserved; [exact known|exact register_476_certificate|exact ran].
Qed.
Lemma divider_pass_rank_progress invalid n old after
 (ranked : (divider_ranked v) n old)
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false old generated_module_0_stmts_0 = Some after) :
 (divider_ranked v) (S n) after.
Proof.
 destruct ranked as [agree [T2 [T8 T9]]].
 destruct T2 as [value2 [found2 typed2]].
 destruct T8 as [value8 [found8 typed8]].
 destruct T9 as [value9 [found9 typed9]]. split.
 - intros id inside bound. apply divider_domain_cases in inside. unfold divider_ids in inside.
   destruct inside as [same|inside].
   + subst id. eapply pass_leaf_0; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_leaf_1; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_output_2; eauto.
   destruct inside as [same|inside].
   + subst id. eapply pass_leaf_3; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_leaf_4; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_leaf_5; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_leaf_6; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_leaf_7; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_output_8; eauto.
   destruct inside as [same|inside].
   + subst id. eapply pass_output_9; eauto.
   destruct inside as [same|inside].
   + subst id. eapply pass_leaf_10; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_leaf_11; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_leaf_12; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_leaf_13; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_14; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_15; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_16; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_17; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_leaf_18; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_19; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_leaf_20; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_21; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_22; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_23; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_24; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_25; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_26; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_27; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_28; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_29; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_30; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_31; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_32; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_leaf_33; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_34; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_35; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_36; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_37; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_leaf_38; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_39; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_leaf_40; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_41; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_42; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_leaf_43; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_44; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_leaf_45; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_leaf_46; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_leaf_47; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_48; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_49; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_50; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_leaf_51; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_52; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_53; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_54; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_55; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_56; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_57; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_58; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_59; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_60; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_61; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_62; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_63; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_64; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_65; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_66; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_67; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_68; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_69; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_70; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_71; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_72; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_73; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_74; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_75; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_76; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_77; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_78; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_79; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_80; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_81; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_82; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_83; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_84; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_85; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_86; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_87; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_88; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_89; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_90; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_91; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_92; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_93; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_94; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_95; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_96; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_97; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_98; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_99; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_100; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_101; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_102; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_103; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_104; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_105; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_106; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_107; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_108; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_109; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_110; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_111; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_112; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_113; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_114; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_115; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_116; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_117; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_118; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_119; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_120; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_121; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_122; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_123; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_124; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_125; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_126; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_127; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_128; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_129; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_130; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_131; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_132; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_133; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_134; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_135; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_136; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_137; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_138; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_139; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_140; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_141; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_142; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_143; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_144; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_145; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_146; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_147; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_148; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_149; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_150; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_151; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_152; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_153; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_154; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_155; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_156; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_157; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_158; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_159; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_160; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_161; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_162; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_163; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_164; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_165; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_166; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_167; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_168; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_169; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_170; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_171; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_172; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_173; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_174; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_175; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_176; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_177; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_178; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_179; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_180; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_181; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_182; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_183; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_184; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_185; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_186; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_187; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_188; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_189; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_190; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_191; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_192; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_193; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_194; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_195; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_196; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_197; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_198; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_199; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_200; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_201; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_202; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_203; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_204; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_205; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_206; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_207; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_208; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_209; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_210; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_211; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_212; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_213; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_214; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_215; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_216; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_217; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_218; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_219; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_220; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_221; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_222; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_223; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_224; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_225; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_226; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_227; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_228; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_229; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_230; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_231; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_232; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_233; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_234; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_235; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_236; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_237; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_238; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_239; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_240; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_241; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_242; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_243; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_244; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_245; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_246; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_247; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_248; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_249; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_250; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_251; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_252; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_253; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_254; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_255; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_256; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_257; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_258; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_259; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_260; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_261; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_262; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_263; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_264; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_265; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_266; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_267; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_268; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_269; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_270; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_271; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_272; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_273; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_274; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_275; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_276; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_277; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_278; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_279; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_280; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_281; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_282; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_283; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_284; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_285; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_286; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_287; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_288; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_289; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_290; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_291; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_292; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_293; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_294; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_295; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_296; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_297; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_298; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_299; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_300; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_301; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_302; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_303; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_304; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_305; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_306; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_307; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_308; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_309; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_310; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_311; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_312; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_313; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_314; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_315; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_316; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_317; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_318; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_319; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_320; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_321; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_322; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_323; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_324; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_325; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_326; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_327; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_328; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_329; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_330; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_331; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_332; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_333; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_334; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_335; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_336; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_337; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_338; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_339; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_340; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_341; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_342; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_343; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_344; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_345; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_346; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_347; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_348; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_349; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_350; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_351; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_352; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_353; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_354; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_355; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_356; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_357; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_358; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_359; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_360; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_361; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_362; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_363; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_364; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_365; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_366; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_367; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_368; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_369; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_370; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_371; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_372; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_373; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_374; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_375; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_376; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_377; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_378; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_379; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_380; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_381; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_382; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_383; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_384; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_385; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_386; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_387; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_388; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_389; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_390; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_391; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_392; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_393; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_394; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_395; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_396; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_397; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_398; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_399; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_400; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_401; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_402; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_403; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_404; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_405; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_406; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_407; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_408; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_409; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_410; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_411; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_412; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_413; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_414; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_415; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_416; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_417; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_418; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_419; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_420; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_421; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_422; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_423; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_424; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_425; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_426; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_427; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_428; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_429; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_430; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_431; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_432; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_433; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_434; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_435; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_436; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_437; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_438; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_439; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_440; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_441; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_442; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_443; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_444; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_leaf_445; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_leaf_446; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_leaf_447; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_448; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_449; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_450; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_451; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_452; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_453; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_454; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_455; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_456; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_457; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_458; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_459; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_460; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_461; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_462; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_463; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_464; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_465; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_466; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_467; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_468; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_469; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_470; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_471; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_472; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_473; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_474; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_leaf_475; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_leaf_476; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_477; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_478; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_479; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_480; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_481; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_482; eassumption.
   destruct inside as [same|inside].
   + subst id. eapply pass_node_483; eassumption.
   contradiction.
 - split; [eapply pass_output_2_type; eassumption|]. split; [eapply pass_output_8_type; eassumption|eapply pass_output_9_type; eassumption].
Qed.
Lemma divider_domain_rank_bound id (inside : divider_domain id) : Nat.le (dependency_rank id) 25.
Proof.
 apply divider_domain_cases in inside. unfold divider_ids in inside.
 repeat destruct inside as [same|inside]; try contradiction; subst id; vm_compute; repeat constructor.
Qed.
Definition divider_circuit_ranked n states := exists env,
 SVM.find [::] states = Some env /\ (divider_ranked v) n env.
Lemma divider_circuit_rank_progress inputs n states final
 (ranked : divider_circuit_ranked n states)
 (ran : circuit_value_iter_with_memory_policy (formal_invalid_policy inputs)
  generated_modules generated_top states false = Some final) :
 divider_circuit_ranked (S n) final.
Proof.
 destruct ranked as [env [Found Ranked]].
 destruct (divider_iteration_local _ _ _ _ ran) as [before [after [Before [Step After]]]].
 rewrite Found in Before. inversion Before; subst before.
 exists after. split; [exact After|]. eapply divider_pass_rank_progress; eassumption.
Qed.
Lemma divider_iterations_ranked inputs count states final
 (ranked : divider_circuit_ranked O states)
 (ran : circuit_formal_iterations generated_modules generated_top inputs count states = Some final) :
 divider_circuit_ranked count final.
Proof.
 have progress := formal_iterations_rank_progress generated_modules generated_top inputs
  divider_circuit_ranked (divider_circuit_rank_progress inputs) count O states final ranked ran.
 rewrite Nat.add_0_r in progress. exact progress.
Qed.
Lemma divider_iterations_converge inputs count states final
 (ranked : divider_circuit_ranked O states)
 (enough : Nat.le 25 count)
 (ran : circuit_formal_iterations generated_modules generated_top inputs count states = Some final) :
 exists env, SVM.find [::] final = Some env /\
 (forall id, divider_domain id -> VM.find id env = VM.find id (stable_env v)) /\ divider_output_types env.
Proof.
 destruct (divider_iterations_ranked inputs count states final ranked ran) as [env [Found [Agree Types]]].
 exists env. split; [exact Found|]. split; [|exact Types].
 intros id inside. apply Agree; [exact inside|].
 have bound := divider_domain_rank_bound id inside. lia.
Qed.
End Progress.
Print Assumptions divider_iterations_converge.
