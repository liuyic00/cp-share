From Coq Require Import NArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import HierarchyFacts PortFieldFacts.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalWidthFacts GlobalNodeSteps GlobalFieldSteps GlobalScalarSteps GlobalSyncSteps GlobalLeaves.
Local Open Scope N_scope.
From SmallMultiplier Require Import GlobalProgressTypes.
From SmallMultiplier Require Export GlobalProgress4.
Lemma global_progress_1000 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(17 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::23] 23 final=Some (Gval (Fuint 2) (global_word_1000 v)).
Proof.
 eapply global_node_1000_step.
 - exact (prior 998%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact (prior 999%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1001 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::23] 24 final=Some (Gval (Fuint 2) (global_word_1001 v)).
Proof.
 eapply global_node_1001_step.
 - exact (prior 1000%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1002 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(19 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::23] 25 final=Some (Gval (Fuint 1) (global_word_1002 v)).
Proof.
 eapply global_node_1002_step.
 - exact (prior 1001%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_1003.
Lemma global_connect_1003_alias v : global_word_1003 v = global_word_1002 v.
Proof. unfold global_word_1003, global_closed_1003, global_expr_1003, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_1003.
Lemma global_progress_1003 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(20 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::23] 4 final=Some (Gval (Fuint 1) (global_word_1003 v)).
Proof.
 have Typed := types 1003%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_1003_step.
 - exact (prior 1002%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (19 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_1003_alias. apply adapt_uint_same. exact (global_size_1002 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1004 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(21 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 23 4 final=Some (Gval (Fuint 1) (global_word_1004 v)).
Proof.
 apply (global_sync_1004_link invalid snapshot final v); [eapply global_progress_1003; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1005 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(22 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 345 final=Some (Gval (Fuint 1) (global_word_1005 v)).
Proof.
 eapply global_node_1005_step.
 - exact (prior 1004%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (21 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1006 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(19 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::23] 26 final=Some (Gval (Fuint 1) (global_word_1006 v)).
Proof.
 eapply global_node_1006_step.
 - exact (prior 1001%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_1007.
Lemma global_connect_1007_alias v : global_word_1007 v = global_word_1006 v.
Proof. unfold global_word_1007, global_closed_1007, global_expr_1007, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_1007.
Lemma global_progress_1007 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(20 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::23] 5 final=Some (Gval (Fuint 1) (global_word_1007 v)).
Proof.
 have Typed := types 1007%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_1007_step.
 - exact (prior 1006%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (19 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_1007_alias. apply adapt_uint_same. exact (global_size_1006 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1008 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(21 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 23 5 final=Some (Gval (Fuint 1) (global_word_1008 v)).
Proof.
 apply (global_sync_1008_link invalid snapshot final v); [eapply global_progress_1007; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1009 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(22 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 346 final=Some (Gval (Fuint 1) (global_word_1009 v)).
Proof.
 eapply global_node_1009_step.
 - exact (prior 1008%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (21 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1010 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 24 2 final=Some (Gval (Fuint 1) (global_word_1010 v)).
Proof.
 have Typed := types 1010%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1010_step.
 - exact (prior 357%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (12 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1010 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1011 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::24] 2 final=Some (Gval (Fuint 1) (global_word_1011 v)).
Proof.
 apply (global_sync_1011_link invalid snapshot final v); [eapply global_progress_1010; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1012 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::24] 19 final=Some (Gval (Fuint 1) (global_word_1012 v)).
Proof.
 eapply global_node_1012_step.
 - exact (prior 1011%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1013 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 24 3 final=Some (Gval (Fuint 1) (global_word_1013 v)).
Proof.
 have Typed := types 1013%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1013_step.
 - exact (prior 337%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (12 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1013 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1014 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::24] 3 final=Some (Gval (Fuint 1) (global_word_1014 v)).
Proof.
 apply (global_sync_1014_link invalid snapshot final v); [eapply global_progress_1013; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1015 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::24] 20 final=Some (Gval (Fuint 1) (global_word_1015 v)).
Proof.
 eapply global_node_1015_step.
 - exact (prior 1014%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1016 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::24] 21 final=Some (Gval (Fuint 1) (global_word_1016 v)).
Proof.
 eapply global_node_1016_step.
 - exact (prior 1012%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 1015%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1017 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::24] 22 final=Some (Gval (Fuint 1) (global_word_1017 v)).
Proof.
 eapply global_node_1017_step.
 - exact (prior 1012%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 1015%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1018 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(17 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::24] 23 final=Some (Gval (Fuint 2) (global_word_1018 v)).
Proof.
 eapply global_node_1018_step.
 - exact (prior 1016%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact (prior 1017%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1019 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::24] 24 final=Some (Gval (Fuint 2) (global_word_1019 v)).
Proof.
 eapply global_node_1019_step.
 - exact (prior 1018%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1020 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(19 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::24] 25 final=Some (Gval (Fuint 1) (global_word_1020 v)).
Proof.
 eapply global_node_1020_step.
 - exact (prior 1019%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_1021.
Lemma global_connect_1021_alias v : global_word_1021 v = global_word_1020 v.
Proof. unfold global_word_1021, global_closed_1021, global_expr_1021, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_1021.
Lemma global_progress_1021 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(20 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::24] 4 final=Some (Gval (Fuint 1) (global_word_1021 v)).
Proof.
 have Typed := types 1021%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_1021_step.
 - exact (prior 1020%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (19 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_1021_alias. apply adapt_uint_same. exact (global_size_1020 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1022 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(21 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 24 4 final=Some (Gval (Fuint 1) (global_word_1022 v)).
Proof.
 apply (global_sync_1022_link invalid snapshot final v); [eapply global_progress_1021; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1023 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(22 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 347 final=Some (Gval (Fuint 1) (global_word_1023 v)).
Proof.
 eapply global_node_1023_step.
 - exact (prior 1022%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (21 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1024 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(19 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::24] 26 final=Some (Gval (Fuint 1) (global_word_1024 v)).
Proof.
 eapply global_node_1024_step.
 - exact (prior 1019%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_1025.
Lemma global_connect_1025_alias v : global_word_1025 v = global_word_1024 v.
Proof. unfold global_word_1025, global_closed_1025, global_expr_1025, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_1025.
Lemma global_progress_1025 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(20 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::24] 5 final=Some (Gval (Fuint 1) (global_word_1025 v)).
Proof.
 have Typed := types 1025%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_1025_step.
 - exact (prior 1024%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (19 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_1025_alias. apply adapt_uint_same. exact (global_size_1024 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1026 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(21 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 24 5 final=Some (Gval (Fuint 1) (global_word_1026 v)).
Proof.
 apply (global_sync_1026_link invalid snapshot final v); [eapply global_progress_1025; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1027 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(22 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 348 final=Some (Gval (Fuint 1) (global_word_1027 v)).
Proof.
 eapply global_node_1027_step.
 - exact (prior 1026%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (21 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1028 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(30 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 25 2 final=Some (Gval (Fuint 1) (global_word_1028 v)).
Proof.
 have Typed := types 1028%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1028_step.
 - exact (prior 416%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (29 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1028 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1029 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(31 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::25] 2 final=Some (Gval (Fuint 1) (global_word_1029 v)).
Proof.
 apply (global_sync_1029_link invalid snapshot final v); [eapply global_progress_1028; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1030 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(32 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::25] 19 final=Some (Gval (Fuint 1) (global_word_1030 v)).
Proof.
 eapply global_node_1030_step.
 - exact (prior 1029%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (31 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1031 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 25 3 final=Some (Gval (Fuint 1) (global_word_1031 v)).
Proof.
 have Typed := types 1031%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1031_step.
 - exact (prior 361%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (12 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1031 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1032 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::25] 3 final=Some (Gval (Fuint 1) (global_word_1032 v)).
Proof.
 apply (global_sync_1032_link invalid snapshot final v); [eapply global_progress_1031; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1033 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::25] 20 final=Some (Gval (Fuint 1) (global_word_1033 v)).
Proof.
 eapply global_node_1033_step.
 - exact (prior 1032%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1034 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(33 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::25] 21 final=Some (Gval (Fuint 1) (global_word_1034 v)).
Proof.
 eapply global_node_1034_step.
 - exact (prior 1030%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (32 <= level)%coq_nat; lia))).
 - exact (prior 1033%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1035 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(33 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::25] 22 final=Some (Gval (Fuint 1) (global_word_1035 v)).
Proof.
 eapply global_node_1035_step.
 - exact (prior 1030%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (32 <= level)%coq_nat; lia))).
 - exact (prior 1033%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1036 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(34 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::25] 23 final=Some (Gval (Fuint 2) (global_word_1036 v)).
Proof.
 eapply global_node_1036_step.
 - exact (prior 1034%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (33 <= level)%coq_nat; lia))).
 - exact (prior 1035%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (33 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1037 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(35 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::25] 24 final=Some (Gval (Fuint 2) (global_word_1037 v)).
Proof.
 eapply global_node_1037_step.
 - exact (prior 1036%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (34 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1038 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(36 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::25] 25 final=Some (Gval (Fuint 1) (global_word_1038 v)).
Proof.
 eapply global_node_1038_step.
 - exact (prior 1037%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (35 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_1039.
Lemma global_connect_1039_alias v : global_word_1039 v = global_word_1038 v.
Proof. unfold global_word_1039, global_closed_1039, global_expr_1039, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_1039.
Lemma global_progress_1039 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(37 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::25] 4 final=Some (Gval (Fuint 1) (global_word_1039 v)).
Proof.
 have Typed := types 1039%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_1039_step.
 - exact (prior 1038%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (36 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_1039_alias. apply adapt_uint_same. exact (global_size_1038 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1040 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(38 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 25 4 final=Some (Gval (Fuint 1) (global_word_1040 v)).
Proof.
 apply (global_sync_1040_link invalid snapshot final v); [eapply global_progress_1039; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1041 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(39 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 349 final=Some (Gval (Fuint 1) (global_word_1041 v)).
Proof.
 eapply global_node_1041_step.
 - exact (prior 1040%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (38 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1042 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(36 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::25] 26 final=Some (Gval (Fuint 1) (global_word_1042 v)).
Proof.
 eapply global_node_1042_step.
 - exact (prior 1037%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (35 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_1043.
Lemma global_connect_1043_alias v : global_word_1043 v = global_word_1042 v.
Proof. unfold global_word_1043, global_closed_1043, global_expr_1043, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_1043.
Lemma global_progress_1043 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(37 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::25] 5 final=Some (Gval (Fuint 1) (global_word_1043 v)).
Proof.
 have Typed := types 1043%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_1043_step.
 - exact (prior 1042%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (36 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_1043_alias. apply adapt_uint_same. exact (global_size_1042 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1044 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(38 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 25 5 final=Some (Gval (Fuint 1) (global_word_1044 v)).
Proof.
 apply (global_sync_1044_link invalid snapshot final v); [eapply global_progress_1043; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1045 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(39 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 350 final=Some (Gval (Fuint 1) (global_word_1045 v)).
Proof.
 eapply global_node_1045_step.
 - exact (prior 1044%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (38 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1046 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(35 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 26 2 final=Some (Gval (Fuint 1) (global_word_1046 v)).
Proof.
 have Typed := types 1046%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1046_step.
 - exact (prior 485%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (34 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1046 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1047 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(36 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::26] 2 final=Some (Gval (Fuint 1) (global_word_1047 v)).
Proof.
 apply (global_sync_1047_link invalid snapshot final v); [eapply global_progress_1046; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1048 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(37 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::26] 19 final=Some (Gval (Fuint 1) (global_word_1048 v)).
Proof.
 eapply global_node_1048_step.
 - exact (prior 1047%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (36 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1049 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(30 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 26 3 final=Some (Gval (Fuint 1) (global_word_1049 v)).
Proof.
 have Typed := types 1049%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1049_step.
 - exact (prior 430%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (29 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1049 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1050 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(31 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::26] 3 final=Some (Gval (Fuint 1) (global_word_1050 v)).
Proof.
 apply (global_sync_1050_link invalid snapshot final v); [eapply global_progress_1049; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1051 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(32 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::26] 20 final=Some (Gval (Fuint 1) (global_word_1051 v)).
Proof.
 eapply global_node_1051_step.
 - exact (prior 1050%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (31 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1052 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(38 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::26] 21 final=Some (Gval (Fuint 1) (global_word_1052 v)).
Proof.
 eapply global_node_1052_step.
 - exact (prior 1048%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact (prior 1051%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (32 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1053 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(38 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::26] 22 final=Some (Gval (Fuint 1) (global_word_1053 v)).
Proof.
 eapply global_node_1053_step.
 - exact (prior 1048%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact (prior 1051%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (32 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1054 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(39 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::26] 23 final=Some (Gval (Fuint 2) (global_word_1054 v)).
Proof.
 eapply global_node_1054_step.
 - exact (prior 1052%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (38 <= level)%coq_nat; lia))).
 - exact (prior 1053%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (38 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1055 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(40 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::26] 24 final=Some (Gval (Fuint 2) (global_word_1055 v)).
Proof.
 eapply global_node_1055_step.
 - exact (prior 1054%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (39 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1056 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(41 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::26] 25 final=Some (Gval (Fuint 1) (global_word_1056 v)).
Proof.
 eapply global_node_1056_step.
 - exact (prior 1055%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (40 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_1057.
Lemma global_connect_1057_alias v : global_word_1057 v = global_word_1056 v.
Proof. unfold global_word_1057, global_closed_1057, global_expr_1057, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_1057.
Lemma global_progress_1057 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(42 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::26] 4 final=Some (Gval (Fuint 1) (global_word_1057 v)).
Proof.
 have Typed := types 1057%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_1057_step.
 - exact (prior 1056%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (41 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_1057_alias. apply adapt_uint_same. exact (global_size_1056 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1058 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(43 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 26 4 final=Some (Gval (Fuint 1) (global_word_1058 v)).
Proof.
 apply (global_sync_1058_link invalid snapshot final v); [eapply global_progress_1057; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1059 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(44 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 351 final=Some (Gval (Fuint 1) (global_word_1059 v)).
Proof.
 eapply global_node_1059_step.
 - exact (prior 1058%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (43 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1060 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(41 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::26] 26 final=Some (Gval (Fuint 1) (global_word_1060 v)).
Proof.
 eapply global_node_1060_step.
 - exact (prior 1055%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (40 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_1061.
Lemma global_connect_1061_alias v : global_word_1061 v = global_word_1060 v.
Proof. unfold global_word_1061, global_closed_1061, global_expr_1061, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_1061.
Lemma global_progress_1061 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(42 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::26] 5 final=Some (Gval (Fuint 1) (global_word_1061 v)).
Proof.
 have Typed := types 1061%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_1061_step.
 - exact (prior 1060%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (41 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_1061_alias. apply adapt_uint_same. exact (global_size_1060 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1062 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(43 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 26 5 final=Some (Gval (Fuint 1) (global_word_1062 v)).
Proof.
 apply (global_sync_1062_link invalid snapshot final v); [eapply global_progress_1061; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1063 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(44 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 352 final=Some (Gval (Fuint 1) (global_word_1063 v)).
Proof.
 eapply global_node_1063_step.
 - exact (prior 1062%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (43 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1064 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(35 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 27 4 final=Some (Gval (Fuint 1) (global_word_1064 v)).
Proof.
 have Typed := types 1064%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1064_step.
 - exact (prior 499%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (34 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1064 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1065 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(36 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 4 final=Some (Gval (Fuint 1) (global_word_1065 v)).
Proof.
 apply (global_sync_1065_link invalid snapshot final v); [eapply global_progress_1064; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1066 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(37 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 25 final=Some (Gval (Fuint 1) (global_word_1066 v)).
Proof.
 eapply global_node_1066_step.
 - exact (prior 1065%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (36 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1067 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(35 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 27 2 final=Some (Gval (Fuint 1) (global_word_1067 v)).
Proof.
 have Typed := types 1067%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1067_step.
 - exact (prior 554%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (34 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1067 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1068 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(36 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 2 final=Some (Gval (Fuint 1) (global_word_1068 v)).
Proof.
 apply (global_sync_1068_link invalid snapshot final v); [eapply global_progress_1067; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1069 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(37 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 23 final=Some (Gval (Fuint 1) (global_word_1069 v)).
Proof.
 eapply global_node_1069_step.
 - exact (prior 1068%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (36 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1070 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 27 3 final=Some (Gval (Fuint 1) (global_word_1070 v)).
Proof.
 have Typed := types 1070%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1070_step.
 - exact (prior 25%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1070 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1071 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 3 final=Some (Gval (Fuint 1) (global_word_1071 v)).
Proof.
 apply (global_sync_1071_link invalid snapshot final v); [eapply global_progress_1070; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1072 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 24 final=Some (Gval (Fuint 1) (global_word_1072 v)).
Proof.
 eapply global_node_1072_step.
 - exact (prior 1071%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1073 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(38 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 26 final=Some (Gval (Fuint 1) (global_word_1073 v)).
Proof.
 eapply global_node_1073_step.
 - exact (prior 1069%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact (prior 1072%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1074 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(39 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 28 final=Some (Gval (Fuint 1) (global_word_1074 v)).
Proof.
 eapply global_node_1074_step.
 - exact (prior 1066%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact (prior 1073%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (38 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1075 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(38 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 27 final=Some (Gval (Fuint 1) (global_word_1075 v)).
Proof.
 eapply global_node_1075_step.
 - exact (prior 1069%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact (prior 1072%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1076 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(39 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 29 final=Some (Gval (Fuint 1) (global_word_1076 v)).
Proof.
 eapply global_node_1076_step.
 - exact (prior 1066%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact (prior 1073%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (38 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1077 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(40 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 30 final=Some (Gval (Fuint 1) (global_word_1077 v)).
Proof.
 eapply global_node_1077_step.
 - exact (prior 1075%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (38 <= level)%coq_nat; lia))).
 - exact (prior 1076%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (39 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1078 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(41 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 31 final=Some (Gval (Fuint 2) (global_word_1078 v)).
Proof.
 eapply global_node_1078_step.
 - exact (prior 1074%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (39 <= level)%coq_nat; lia))).
 - exact (prior 1077%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (40 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1079 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(42 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 32 final=Some (Gval (Fuint 2) (global_word_1079 v)).
Proof.
 eapply global_node_1079_step.
 - exact (prior 1078%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (41 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1080 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(43 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 33 final=Some (Gval (Fuint 1) (global_word_1080 v)).
Proof.
 eapply global_node_1080_step.
 - exact (prior 1079%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (42 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_1081.
Lemma global_connect_1081_alias v : global_word_1081 v = global_word_1080 v.
Proof. unfold global_word_1081, global_closed_1081, global_expr_1081, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_1081.
Lemma global_progress_1081 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(44 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 5 final=Some (Gval (Fuint 1) (global_word_1081 v)).
Proof.
 have Typed := types 1081%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_1081_step.
 - exact (prior 1080%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (43 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_1081_alias. apply adapt_uint_same. exact (global_size_1080 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1082 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(45 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 27 5 final=Some (Gval (Fuint 1) (global_word_1082 v)).
Proof.
 apply (global_sync_1082_link invalid snapshot final v); [eapply global_progress_1081; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1083 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(46 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 353 final=Some (Gval (Fuint 1) (global_word_1083 v)).
Proof.
 eapply global_node_1083_step.
 - exact (prior 1082%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (45 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1084 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(43 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 34 final=Some (Gval (Fuint 1) (global_word_1084 v)).
Proof.
 eapply global_node_1084_step.
 - exact (prior 1079%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (42 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_1085.
Lemma global_connect_1085_alias v : global_word_1085 v = global_word_1084 v.
Proof. unfold global_word_1085, global_closed_1085, global_expr_1085, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_1085.
Lemma global_progress_1085 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(44 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 6 final=Some (Gval (Fuint 1) (global_word_1085 v)).
Proof.
 have Typed := types 1085%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_1085_step.
 - exact (prior 1084%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (43 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_1085_alias. apply adapt_uint_same. exact (global_size_1084 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1086 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(45 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 27 6 final=Some (Gval (Fuint 1) (global_word_1086 v)).
Proof.
 apply (global_sync_1086_link invalid snapshot final v); [eapply global_progress_1085; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1087 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(46 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 354 final=Some (Gval (Fuint 1) (global_word_1087 v)).
Proof.
 eapply global_node_1087_step.
 - exact (prior 1086%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (45 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1088 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(35 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 28 4 final=Some (Gval (Fuint 1) (global_word_1088 v)).
Proof.
 have Typed := types 1088%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1088_step.
 - exact (prior 568%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (34 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1088 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1089 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(36 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 4 final=Some (Gval (Fuint 1) (global_word_1089 v)).
Proof.
 apply (global_sync_1089_link invalid snapshot final v); [eapply global_progress_1088; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1090 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(37 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 25 final=Some (Gval (Fuint 1) (global_word_1090 v)).
Proof.
 eapply global_node_1090_step.
 - exact (prior 1089%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (36 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1091 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(35 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 28 2 final=Some (Gval (Fuint 1) (global_word_1091 v)).
Proof.
 have Typed := types 1091%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1091_step.
 - exact (prior 623%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (34 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1091 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1092 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(36 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 2 final=Some (Gval (Fuint 1) (global_word_1092 v)).
Proof.
 apply (global_sync_1092_link invalid snapshot final v); [eapply global_progress_1091; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1093 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(37 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 23 final=Some (Gval (Fuint 1) (global_word_1093 v)).
Proof.
 eapply global_node_1093_step.
 - exact (prior 1092%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (36 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1094 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 28 3 final=Some (Gval (Fuint 1) (global_word_1094 v)).
Proof.
 have Typed := types 1094%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1094_step.
 - exact (prior 30%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1094 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1095 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 3 final=Some (Gval (Fuint 1) (global_word_1095 v)).
Proof.
 apply (global_sync_1095_link invalid snapshot final v); [eapply global_progress_1094; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1096 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 24 final=Some (Gval (Fuint 1) (global_word_1096 v)).
Proof.
 eapply global_node_1096_step.
 - exact (prior 1095%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1097 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(38 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 26 final=Some (Gval (Fuint 1) (global_word_1097 v)).
Proof.
 eapply global_node_1097_step.
 - exact (prior 1093%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact (prior 1096%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1098 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(39 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 28 final=Some (Gval (Fuint 1) (global_word_1098 v)).
Proof.
 eapply global_node_1098_step.
 - exact (prior 1090%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact (prior 1097%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (38 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1099 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(38 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 27 final=Some (Gval (Fuint 1) (global_word_1099 v)).
Proof.
 eapply global_node_1099_step.
 - exact (prior 1093%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact (prior 1096%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1100 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(39 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 29 final=Some (Gval (Fuint 1) (global_word_1100 v)).
Proof.
 eapply global_node_1100_step.
 - exact (prior 1090%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact (prior 1097%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (38 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1101 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(40 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 30 final=Some (Gval (Fuint 1) (global_word_1101 v)).
Proof.
 eapply global_node_1101_step.
 - exact (prior 1099%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (38 <= level)%coq_nat; lia))).
 - exact (prior 1100%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (39 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1102 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(41 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 31 final=Some (Gval (Fuint 2) (global_word_1102 v)).
Proof.
 eapply global_node_1102_step.
 - exact (prior 1098%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (39 <= level)%coq_nat; lia))).
 - exact (prior 1101%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (40 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1103 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(42 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 32 final=Some (Gval (Fuint 2) (global_word_1103 v)).
Proof.
 eapply global_node_1103_step.
 - exact (prior 1102%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (41 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1104 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(43 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 33 final=Some (Gval (Fuint 1) (global_word_1104 v)).
Proof.
 eapply global_node_1104_step.
 - exact (prior 1103%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (42 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_1105.
Lemma global_connect_1105_alias v : global_word_1105 v = global_word_1104 v.
Proof. unfold global_word_1105, global_closed_1105, global_expr_1105, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_1105.
Lemma global_progress_1105 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(44 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 5 final=Some (Gval (Fuint 1) (global_word_1105 v)).
Proof.
 have Typed := types 1105%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_1105_step.
 - exact (prior 1104%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (43 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_1105_alias. apply adapt_uint_same. exact (global_size_1104 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1106 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(45 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 28 5 final=Some (Gval (Fuint 1) (global_word_1106 v)).
Proof.
 apply (global_sync_1106_link invalid snapshot final v); [eapply global_progress_1105; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1107 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(46 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 355 final=Some (Gval (Fuint 1) (global_word_1107 v)).
Proof.
 eapply global_node_1107_step.
 - exact (prior 1106%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (45 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1108 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(43 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 34 final=Some (Gval (Fuint 1) (global_word_1108 v)).
Proof.
 eapply global_node_1108_step.
 - exact (prior 1103%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (42 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_1109.
Lemma global_connect_1109_alias v : global_word_1109 v = global_word_1108 v.
Proof. unfold global_word_1109, global_closed_1109, global_expr_1109, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_1109.
Lemma global_progress_1109 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(44 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 6 final=Some (Gval (Fuint 1) (global_word_1109 v)).
Proof.
 have Typed := types 1109%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_1109_step.
 - exact (prior 1108%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (43 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_1109_alias. apply adapt_uint_same. exact (global_size_1108 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1110 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(45 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 28 6 final=Some (Gval (Fuint 1) (global_word_1110 v)).
Proof.
 apply (global_sync_1110_link invalid snapshot final v); [eapply global_progress_1109; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1111 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(46 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 356 final=Some (Gval (Fuint 1) (global_word_1111 v)).
Proof.
 eapply global_node_1111_step.
 - exact (prior 1110%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (45 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1112 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(35 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 29 2 final=Some (Gval (Fuint 1) (global_word_1112 v)).
Proof.
 have Typed := types 1112%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1112_step.
 - exact (prior 692%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (34 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1112 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1113 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(36 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::29] 2 final=Some (Gval (Fuint 1) (global_word_1113 v)).
Proof.
 apply (global_sync_1113_link invalid snapshot final v); [eapply global_progress_1112; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1114 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(37 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::29] 19 final=Some (Gval (Fuint 1) (global_word_1114 v)).
Proof.
 eapply global_node_1114_step.
 - exact (prior 1113%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (36 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1115 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(35 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 29 3 final=Some (Gval (Fuint 1) (global_word_1115 v)).
Proof.
 have Typed := types 1115%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1115_step.
 - exact (prior 637%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (34 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1115 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1116 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(36 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::29] 3 final=Some (Gval (Fuint 1) (global_word_1116 v)).
Proof.
 apply (global_sync_1116_link invalid snapshot final v); [eapply global_progress_1115; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1117 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(37 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::29] 20 final=Some (Gval (Fuint 1) (global_word_1117 v)).
Proof.
 eapply global_node_1117_step.
 - exact (prior 1116%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (36 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1118 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(38 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::29] 21 final=Some (Gval (Fuint 1) (global_word_1118 v)).
Proof.
 eapply global_node_1118_step.
 - exact (prior 1114%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact (prior 1117%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1119 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(38 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::29] 22 final=Some (Gval (Fuint 1) (global_word_1119 v)).
Proof.
 eapply global_node_1119_step.
 - exact (prior 1114%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact (prior 1117%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1120 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(39 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::29] 23 final=Some (Gval (Fuint 2) (global_word_1120 v)).
Proof.
 eapply global_node_1120_step.
 - exact (prior 1118%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (38 <= level)%coq_nat; lia))).
 - exact (prior 1119%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (38 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1121 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(40 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::29] 24 final=Some (Gval (Fuint 2) (global_word_1121 v)).
Proof.
 eapply global_node_1121_step.
 - exact (prior 1120%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (39 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1122 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(41 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::29] 25 final=Some (Gval (Fuint 1) (global_word_1122 v)).
Proof.
 eapply global_node_1122_step.
 - exact (prior 1121%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (40 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_1123.
Lemma global_connect_1123_alias v : global_word_1123 v = global_word_1122 v.
Proof. unfold global_word_1123, global_closed_1123, global_expr_1123, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_1123.
Lemma global_progress_1123 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(42 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::29] 4 final=Some (Gval (Fuint 1) (global_word_1123 v)).
Proof.
 have Typed := types 1123%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_1123_step.
 - exact (prior 1122%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (41 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_1123_alias. apply adapt_uint_same. exact (global_size_1122 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1124 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(43 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 29 4 final=Some (Gval (Fuint 1) (global_word_1124 v)).
Proof.
 apply (global_sync_1124_link invalid snapshot final v); [eapply global_progress_1123; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1125 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(44 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 357 final=Some (Gval (Fuint 1) (global_word_1125 v)).
Proof.
 eapply global_node_1125_step.
 - exact (prior 1124%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (43 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1126 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(41 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::29] 26 final=Some (Gval (Fuint 1) (global_word_1126 v)).
Proof.
 eapply global_node_1126_step.
 - exact (prior 1121%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (40 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_1127.
Lemma global_connect_1127_alias v : global_word_1127 v = global_word_1126 v.
Proof. unfold global_word_1127, global_closed_1127, global_expr_1127, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_1127.
Lemma global_progress_1127 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(42 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::29] 5 final=Some (Gval (Fuint 1) (global_word_1127 v)).
Proof.
 have Typed := types 1127%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_1127_step.
 - exact (prior 1126%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (41 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_1127_alias. apply adapt_uint_same. exact (global_size_1126 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1128 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(43 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 29 5 final=Some (Gval (Fuint 1) (global_word_1128 v)).
Proof.
 apply (global_sync_1128_link invalid snapshot final v); [eapply global_progress_1127; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1129 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(44 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 358 final=Some (Gval (Fuint 1) (global_word_1129 v)).
Proof.
 eapply global_node_1129_step.
 - exact (prior 1128%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (43 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1130 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(35 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 30 2 final=Some (Gval (Fuint 1) (global_word_1130 v)).
Proof.
 have Typed := types 1130%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1130_step.
 - exact (prior 761%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (34 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1130 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1131 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(36 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::30] 2 final=Some (Gval (Fuint 1) (global_word_1131 v)).
Proof.
 apply (global_sync_1131_link invalid snapshot final v); [eapply global_progress_1130; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1132 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(37 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::30] 19 final=Some (Gval (Fuint 1) (global_word_1132 v)).
Proof.
 eapply global_node_1132_step.
 - exact (prior 1131%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (36 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1133 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(35 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 30 3 final=Some (Gval (Fuint 1) (global_word_1133 v)).
Proof.
 have Typed := types 1133%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1133_step.
 - exact (prior 706%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (34 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1133 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1134 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(36 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::30] 3 final=Some (Gval (Fuint 1) (global_word_1134 v)).
Proof.
 apply (global_sync_1134_link invalid snapshot final v); [eapply global_progress_1133; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1135 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(37 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::30] 20 final=Some (Gval (Fuint 1) (global_word_1135 v)).
Proof.
 eapply global_node_1135_step.
 - exact (prior 1134%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (36 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1136 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(38 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::30] 21 final=Some (Gval (Fuint 1) (global_word_1136 v)).
Proof.
 eapply global_node_1136_step.
 - exact (prior 1132%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact (prior 1135%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1137 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(38 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::30] 22 final=Some (Gval (Fuint 1) (global_word_1137 v)).
Proof.
 eapply global_node_1137_step.
 - exact (prior 1132%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact (prior 1135%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1138 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(39 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::30] 23 final=Some (Gval (Fuint 2) (global_word_1138 v)).
Proof.
 eapply global_node_1138_step.
 - exact (prior 1136%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (38 <= level)%coq_nat; lia))).
 - exact (prior 1137%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (38 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1139 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(40 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::30] 24 final=Some (Gval (Fuint 2) (global_word_1139 v)).
Proof.
 eapply global_node_1139_step.
 - exact (prior 1138%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (39 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1140 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(41 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::30] 25 final=Some (Gval (Fuint 1) (global_word_1140 v)).
Proof.
 eapply global_node_1140_step.
 - exact (prior 1139%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (40 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_1141.
Lemma global_connect_1141_alias v : global_word_1141 v = global_word_1140 v.
Proof. unfold global_word_1141, global_closed_1141, global_expr_1141, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_1141.
Lemma global_progress_1141 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(42 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::30] 4 final=Some (Gval (Fuint 1) (global_word_1141 v)).
Proof.
 have Typed := types 1141%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_1141_step.
 - exact (prior 1140%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (41 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_1141_alias. apply adapt_uint_same. exact (global_size_1140 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1142 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(43 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 30 4 final=Some (Gval (Fuint 1) (global_word_1142 v)).
Proof.
 apply (global_sync_1142_link invalid snapshot final v); [eapply global_progress_1141; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1143 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(44 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 359 final=Some (Gval (Fuint 1) (global_word_1143 v)).
Proof.
 eapply global_node_1143_step.
 - exact (prior 1142%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (43 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1144 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(41 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::30] 26 final=Some (Gval (Fuint 1) (global_word_1144 v)).
Proof.
 eapply global_node_1144_step.
 - exact (prior 1139%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (40 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_1145.
Lemma global_connect_1145_alias v : global_word_1145 v = global_word_1144 v.
Proof. unfold global_word_1145, global_closed_1145, global_expr_1145, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_1145.
Lemma global_progress_1145 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(42 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::30] 5 final=Some (Gval (Fuint 1) (global_word_1145 v)).
Proof.
 have Typed := types 1145%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_1145_step.
 - exact (prior 1144%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (41 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_1145_alias. apply adapt_uint_same. exact (global_size_1144 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1146 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(43 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 30 5 final=Some (Gval (Fuint 1) (global_word_1146 v)).
Proof.
 apply (global_sync_1146_link invalid snapshot final v); [eapply global_progress_1145; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1147 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(44 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 360 final=Some (Gval (Fuint 1) (global_word_1147 v)).
Proof.
 eapply global_node_1147_step.
 - exact (prior 1146%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (43 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1148 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(35 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 31 2 final=Some (Gval (Fuint 1) (global_word_1148 v)).
Proof.
 have Typed := types 1148%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1148_step.
 - exact (prior 830%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (34 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1148 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1149 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(36 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::31] 2 final=Some (Gval (Fuint 1) (global_word_1149 v)).
Proof.
 apply (global_sync_1149_link invalid snapshot final v); [eapply global_progress_1148; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1150 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(37 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::31] 19 final=Some (Gval (Fuint 1) (global_word_1150 v)).
Proof.
 eapply global_node_1150_step.
 - exact (prior 1149%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (36 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1151 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(35 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 31 3 final=Some (Gval (Fuint 1) (global_word_1151 v)).
Proof.
 have Typed := types 1151%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1151_step.
 - exact (prior 775%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (34 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1151 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1152 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(36 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::31] 3 final=Some (Gval (Fuint 1) (global_word_1152 v)).
Proof.
 apply (global_sync_1152_link invalid snapshot final v); [eapply global_progress_1151; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1153 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(37 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::31] 20 final=Some (Gval (Fuint 1) (global_word_1153 v)).
Proof.
 eapply global_node_1153_step.
 - exact (prior 1152%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (36 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1154 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(38 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::31] 21 final=Some (Gval (Fuint 1) (global_word_1154 v)).
Proof.
 eapply global_node_1154_step.
 - exact (prior 1150%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact (prior 1153%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1155 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(38 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::31] 22 final=Some (Gval (Fuint 1) (global_word_1155 v)).
Proof.
 eapply global_node_1155_step.
 - exact (prior 1150%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact (prior 1153%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1156 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(39 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::31] 23 final=Some (Gval (Fuint 2) (global_word_1156 v)).
Proof.
 eapply global_node_1156_step.
 - exact (prior 1154%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (38 <= level)%coq_nat; lia))).
 - exact (prior 1155%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (38 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1157 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(40 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::31] 24 final=Some (Gval (Fuint 2) (global_word_1157 v)).
Proof.
 eapply global_node_1157_step.
 - exact (prior 1156%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (39 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1158 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(41 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::31] 25 final=Some (Gval (Fuint 1) (global_word_1158 v)).
Proof.
 eapply global_node_1158_step.
 - exact (prior 1157%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (40 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_1159.
Lemma global_connect_1159_alias v : global_word_1159 v = global_word_1158 v.
Proof. unfold global_word_1159, global_closed_1159, global_expr_1159, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_1159.
Lemma global_progress_1159 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(42 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::31] 4 final=Some (Gval (Fuint 1) (global_word_1159 v)).
Proof.
 have Typed := types 1159%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_1159_step.
 - exact (prior 1158%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (41 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_1159_alias. apply adapt_uint_same. exact (global_size_1158 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1160 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(43 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 31 4 final=Some (Gval (Fuint 1) (global_word_1160 v)).
Proof.
 apply (global_sync_1160_link invalid snapshot final v); [eapply global_progress_1159; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1161 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(44 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 361 final=Some (Gval (Fuint 1) (global_word_1161 v)).
Proof.
 eapply global_node_1161_step.
 - exact (prior 1160%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (43 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1162 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(41 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::31] 26 final=Some (Gval (Fuint 1) (global_word_1162 v)).
Proof.
 eapply global_node_1162_step.
 - exact (prior 1157%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (40 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_1163.
Lemma global_connect_1163_alias v : global_word_1163 v = global_word_1162 v.
Proof. unfold global_word_1163, global_closed_1163, global_expr_1163, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_1163.
Lemma global_progress_1163 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(42 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::31] 5 final=Some (Gval (Fuint 1) (global_word_1163 v)).
Proof.
 have Typed := types 1163%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_1163_step.
 - exact (prior 1162%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (41 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_1163_alias. apply adapt_uint_same. exact (global_size_1162 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1164 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(43 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 31 5 final=Some (Gval (Fuint 1) (global_word_1164 v)).
Proof.
 apply (global_sync_1164_link invalid snapshot final v); [eapply global_progress_1163; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1165 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(44 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 362 final=Some (Gval (Fuint 1) (global_word_1165 v)).
Proof.
 eapply global_node_1165_step.
 - exact (prior 1164%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (43 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1166 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(35 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 32 2 final=Some (Gval (Fuint 1) (global_word_1166 v)).
Proof.
 have Typed := types 1166%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1166_step.
 - exact (prior 899%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (34 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1166 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1167 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(36 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::32] 2 final=Some (Gval (Fuint 1) (global_word_1167 v)).
Proof.
 apply (global_sync_1167_link invalid snapshot final v); [eapply global_progress_1166; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1168 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(37 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::32] 19 final=Some (Gval (Fuint 1) (global_word_1168 v)).
Proof.
 eapply global_node_1168_step.
 - exact (prior 1167%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (36 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1169 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(35 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 32 3 final=Some (Gval (Fuint 1) (global_word_1169 v)).
Proof.
 have Typed := types 1169%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1169_step.
 - exact (prior 844%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (34 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1169 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1170 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(36 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::32] 3 final=Some (Gval (Fuint 1) (global_word_1170 v)).
Proof.
 apply (global_sync_1170_link invalid snapshot final v); [eapply global_progress_1169; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1171 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(37 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::32] 20 final=Some (Gval (Fuint 1) (global_word_1171 v)).
Proof.
 eapply global_node_1171_step.
 - exact (prior 1170%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (36 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1172 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(38 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::32] 21 final=Some (Gval (Fuint 1) (global_word_1172 v)).
Proof.
 eapply global_node_1172_step.
 - exact (prior 1168%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact (prior 1171%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1173 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(38 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::32] 22 final=Some (Gval (Fuint 1) (global_word_1173 v)).
Proof.
 eapply global_node_1173_step.
 - exact (prior 1168%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact (prior 1171%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1174 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(39 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::32] 23 final=Some (Gval (Fuint 2) (global_word_1174 v)).
Proof.
 eapply global_node_1174_step.
 - exact (prior 1172%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (38 <= level)%coq_nat; lia))).
 - exact (prior 1173%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (38 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1175 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(40 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::32] 24 final=Some (Gval (Fuint 2) (global_word_1175 v)).
Proof.
 eapply global_node_1175_step.
 - exact (prior 1174%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (39 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1176 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(41 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::32] 25 final=Some (Gval (Fuint 1) (global_word_1176 v)).
Proof.
 eapply global_node_1176_step.
 - exact (prior 1175%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (40 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_1177.
Lemma global_connect_1177_alias v : global_word_1177 v = global_word_1176 v.
Proof. unfold global_word_1177, global_closed_1177, global_expr_1177, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_1177.
Lemma global_progress_1177 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(42 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::32] 4 final=Some (Gval (Fuint 1) (global_word_1177 v)).
Proof.
 have Typed := types 1177%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_1177_step.
 - exact (prior 1176%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (41 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_1177_alias. apply adapt_uint_same. exact (global_size_1176 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1178 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(43 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 32 4 final=Some (Gval (Fuint 1) (global_word_1178 v)).
Proof.
 apply (global_sync_1178_link invalid snapshot final v); [eapply global_progress_1177; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1179 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(44 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 363 final=Some (Gval (Fuint 1) (global_word_1179 v)).
Proof.
 eapply global_node_1179_step.
 - exact (prior 1178%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (43 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1180 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(41 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::32] 26 final=Some (Gval (Fuint 1) (global_word_1180 v)).
Proof.
 eapply global_node_1180_step.
 - exact (prior 1175%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (40 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_1181.
Lemma global_connect_1181_alias v : global_word_1181 v = global_word_1180 v.
Proof. unfold global_word_1181, global_closed_1181, global_expr_1181, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_1181.
Lemma global_progress_1181 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(42 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::32] 5 final=Some (Gval (Fuint 1) (global_word_1181 v)).
Proof.
 have Typed := types 1181%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_1181_step.
 - exact (prior 1180%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (41 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_1181_alias. apply adapt_uint_same. exact (global_size_1180 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1182 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(43 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 32 5 final=Some (Gval (Fuint 1) (global_word_1182 v)).
Proof.
 apply (global_sync_1182_link invalid snapshot final v); [eapply global_progress_1181; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1183 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(44 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 364 final=Some (Gval (Fuint 1) (global_word_1183 v)).
Proof.
 eapply global_node_1183_step.
 - exact (prior 1182%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (43 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1184 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(35 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 33 4 final=Some (Gval (Fuint 1) (global_word_1184 v)).
Proof.
 have Typed := types 1184%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1184_step.
 - exact (prior 913%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (34 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1184 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1185 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(36 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 4 final=Some (Gval (Fuint 1) (global_word_1185 v)).
Proof.
 apply (global_sync_1185_link invalid snapshot final v); [eapply global_progress_1184; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1186 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(37 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 25 final=Some (Gval (Fuint 1) (global_word_1186 v)).
Proof.
 eapply global_node_1186_step.
 - exact (prior 1185%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (36 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1187 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 33 2 final=Some (Gval (Fuint 1) (global_word_1187 v)).
Proof.
 have Typed := types 1187%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1187_step.
 - exact (prior 933%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (12 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1187 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1188 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 2 final=Some (Gval (Fuint 1) (global_word_1188 v)).
Proof.
 apply (global_sync_1188_link invalid snapshot final v); [eapply global_progress_1187; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1189 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 23 final=Some (Gval (Fuint 1) (global_word_1189 v)).
Proof.
 eapply global_node_1189_step.
 - exact (prior 1188%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1190 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 33 3 final=Some (Gval (Fuint 1) (global_word_1190 v)).
Proof.
 have Typed := types 1190%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1190_step.
 - exact (prior 906%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1190 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1191 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(19 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 3 final=Some (Gval (Fuint 1) (global_word_1191 v)).
Proof.
 apply (global_sync_1191_link invalid snapshot final v); [eapply global_progress_1190; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1192 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(20 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 24 final=Some (Gval (Fuint 1) (global_word_1192 v)).
Proof.
 eapply global_node_1192_step.
 - exact (prior 1191%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (19 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1193 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(21 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 26 final=Some (Gval (Fuint 1) (global_word_1193 v)).
Proof.
 eapply global_node_1193_step.
 - exact (prior 1189%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 1192%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (20 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1194 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(38 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 28 final=Some (Gval (Fuint 1) (global_word_1194 v)).
Proof.
 eapply global_node_1194_step.
 - exact (prior 1186%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact (prior 1193%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (21 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1195 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(21 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 27 final=Some (Gval (Fuint 1) (global_word_1195 v)).
Proof.
 eapply global_node_1195_step.
 - exact (prior 1189%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 1192%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (20 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1196 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(38 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 29 final=Some (Gval (Fuint 1) (global_word_1196 v)).
Proof.
 eapply global_node_1196_step.
 - exact (prior 1186%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact (prior 1193%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (21 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1197 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(39 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 30 final=Some (Gval (Fuint 1) (global_word_1197 v)).
Proof.
 eapply global_node_1197_step.
 - exact (prior 1195%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (21 <= level)%coq_nat; lia))).
 - exact (prior 1196%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (38 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1198 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(40 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 31 final=Some (Gval (Fuint 2) (global_word_1198 v)).
Proof.
 eapply global_node_1198_step.
 - exact (prior 1194%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (38 <= level)%coq_nat; lia))).
 - exact (prior 1197%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (39 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1199 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(41 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 32 final=Some (Gval (Fuint 2) (global_word_1199 v)).
Proof.
 eapply global_node_1199_step.
 - exact (prior 1198%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (40 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
