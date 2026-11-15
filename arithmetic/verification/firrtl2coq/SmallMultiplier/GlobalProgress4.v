From Coq Require Import NArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import HierarchyFacts PortFieldFacts.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalWidthFacts GlobalNodeSteps GlobalFieldSteps GlobalScalarSteps GlobalSyncSteps GlobalLeaves.
Local Open Scope N_scope.
From SmallMultiplier Require Import GlobalProgressTypes.
From SmallMultiplier Require Export GlobalProgress3.
Lemma global_progress_800 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(7 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 29 final=Some (Gval (Fuint 1) (global_word_800 v)).
Proof.
 eapply global_node_800_step.
 - exact (prior 786%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 797%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_801 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(8 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 30 final=Some (Gval (Fuint 1) (global_word_801 v)).
Proof.
 eapply global_node_801_step.
 - exact (prior 799%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact (prior 800%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (7 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_802 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(9 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 31 final=Some (Gval (Fuint 2) (global_word_802 v)).
Proof.
 eapply global_node_802_step.
 - exact (prior 798%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (7 <= level)%coq_nat; lia))).
 - exact (prior 801%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (8 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_803 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(10 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 32 final=Some (Gval (Fuint 2) (global_word_803 v)).
Proof.
 eapply global_node_803_step.
 - exact (prior 802%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (9 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_804 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(11 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 33 final=Some (Gval (Fuint 1) (global_word_804 v)).
Proof.
 eapply global_node_804_step.
 - exact (prior 803%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (10 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_805.
Lemma global_connect_805_alias v : global_word_805 v = global_word_804 v.
Proof. unfold global_word_805, global_closed_805, global_expr_805, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_805.
Lemma global_progress_805 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(12 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 5 final=Some (Gval (Fuint 1) (global_word_805 v)).
Proof.
 have Typed := types 805%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_805_step.
 - exact (prior 804%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (11 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_805_alias. apply adapt_uint_same. exact (global_size_804 v sizes).
 - exact ran.
Qed.
Lemma global_progress_806 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::17] 10 5 final=Some (Gval (Fuint 1) (global_word_806 v)).
Proof.
 apply (global_sync_806_link invalid snapshot final v); [eapply global_progress_805; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_807 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 38 final=Some (Gval (Fuint 1) (global_word_807 v)).
Proof.
 eapply global_node_807_step.
 - exact (prior 806%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_808 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::17] 11 2 final=Some (Gval (Fuint 1) (global_word_808 v)).
Proof.
 have Typed := types 808%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_808_step.
 - exact (prior 807%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_808 v sizes).
 - exact ran.
Qed.
Lemma global_progress_809 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 2 final=Some (Gval (Fuint 1) (global_word_809 v)).
Proof.
 apply (global_sync_809_link invalid snapshot final v); [eapply global_progress_808; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_810 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(17 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 23 final=Some (Gval (Fuint 1) (global_word_810 v)).
Proof.
 eapply global_node_810_step.
 - exact (prior 809%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_811 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 17 5 final=Some (Gval (Fuint 1) (global_word_811 v)).
Proof.
 have Typed := types 811%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_811_step.
 - exact (prior 42%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_811 v sizes).
 - exact ran.
Qed.
Lemma global_progress_812 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 5 final=Some (Gval (Fuint 1) (global_word_812 v)).
Proof.
 apply (global_sync_812_link invalid snapshot final v); [eapply global_progress_811; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_813 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 39 final=Some (Gval (Fuint 1) (global_word_813 v)).
Proof.
 eapply global_node_813_step.
 - exact (prior 812%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_814 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::17] 11 3 final=Some (Gval (Fuint 1) (global_word_814 v)).
Proof.
 have Typed := types 814%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_814_step.
 - exact (prior 813%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_814 v sizes).
 - exact ran.
Qed.
Lemma global_progress_815 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 3 final=Some (Gval (Fuint 1) (global_word_815 v)).
Proof.
 apply (global_sync_815_link invalid snapshot final v); [eapply global_progress_814; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_816 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 24 final=Some (Gval (Fuint 1) (global_word_816 v)).
Proof.
 eapply global_node_816_step.
 - exact (prior 815%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_817 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 26 final=Some (Gval (Fuint 1) (global_word_817 v)).
Proof.
 eapply global_node_817_step.
 - exact (prior 810%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact (prior 816%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_818 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(24 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 28 final=Some (Gval (Fuint 1) (global_word_818 v)).
Proof.
 eapply global_node_818_step.
 - exact (prior 781%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (23 <= level)%coq_nat; lia))).
 - exact (prior 817%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_819 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 27 final=Some (Gval (Fuint 1) (global_word_819 v)).
Proof.
 eapply global_node_819_step.
 - exact (prior 810%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact (prior 816%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_820 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(24 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 29 final=Some (Gval (Fuint 1) (global_word_820 v)).
Proof.
 eapply global_node_820_step.
 - exact (prior 781%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (23 <= level)%coq_nat; lia))).
 - exact (prior 817%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_821 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(25 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 30 final=Some (Gval (Fuint 1) (global_word_821 v)).
Proof.
 eapply global_node_821_step.
 - exact (prior 819%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact (prior 820%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (24 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_822 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(26 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 31 final=Some (Gval (Fuint 2) (global_word_822 v)).
Proof.
 eapply global_node_822_step.
 - exact (prior 818%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (24 <= level)%coq_nat; lia))).
 - exact (prior 821%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (25 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_823 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(27 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 32 final=Some (Gval (Fuint 2) (global_word_823 v)).
Proof.
 eapply global_node_823_step.
 - exact (prior 822%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (26 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_824 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(28 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 33 final=Some (Gval (Fuint 1) (global_word_824 v)).
Proof.
 eapply global_node_824_step.
 - exact (prior 823%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (27 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_825.
Lemma global_connect_825_alias v : global_word_825 v = global_word_824 v.
Proof. unfold global_word_825, global_closed_825, global_expr_825, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_825.
Lemma global_progress_825 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(29 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 5 final=Some (Gval (Fuint 1) (global_word_825 v)).
Proof.
 have Typed := types 825%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_825_step.
 - exact (prior 824%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (28 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_825_alias. apply adapt_uint_same. exact (global_size_824 v sizes).
 - exact ran.
Qed.
Lemma global_progress_826 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(30 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::17] 11 5 final=Some (Gval (Fuint 1) (global_word_826 v)).
Proof.
 apply (global_sync_826_link invalid snapshot final v); [eapply global_progress_825; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_827 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(31 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 41 final=Some (Gval (Fuint 1) (global_word_827 v)).
Proof.
 eapply global_node_827_step.
 - exact (prior 826%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (30 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_828.
Lemma global_connect_828_alias v : global_word_828 v = global_word_827 v.
Proof. unfold global_word_828, global_closed_828, global_expr_828, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_828.
Lemma global_progress_828 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(32 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 7 final=Some (Gval (Fuint 1) (global_word_828 v)).
Proof.
 have Typed := types 828%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_828_step.
 - exact (prior 827%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (31 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_828_alias. apply adapt_uint_same. exact (global_size_827 v sizes).
 - exact ran.
Qed.
Lemma global_progress_829 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(33 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 17 7 final=Some (Gval (Fuint 1) (global_word_829 v)).
Proof.
 apply (global_sync_829_link invalid snapshot final v); [eapply global_progress_828; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_830 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(34 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 331 final=Some (Gval (Fuint 1) (global_word_830 v)).
Proof.
 eapply global_node_830_step.
 - exact (prior 829%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (33 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_831 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(11 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 34 final=Some (Gval (Fuint 1) (global_word_831 v)).
Proof.
 eapply global_node_831_step.
 - exact (prior 803%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (10 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_832.
Lemma global_connect_832_alias v : global_word_832 v = global_word_831 v.
Proof. unfold global_word_832, global_closed_832, global_expr_832, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_832.
Lemma global_progress_832 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(12 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 6 final=Some (Gval (Fuint 1) (global_word_832 v)).
Proof.
 have Typed := types 832%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_832_step.
 - exact (prior 831%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (11 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_832_alias. apply adapt_uint_same. exact (global_size_831 v sizes).
 - exact ran.
Qed.
Lemma global_progress_833 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::17] 10 6 final=Some (Gval (Fuint 1) (global_word_833 v)).
Proof.
 apply (global_sync_833_link invalid snapshot final v); [eapply global_progress_832; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_834 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 42 final=Some (Gval (Fuint 1) (global_word_834 v)).
Proof.
 eapply global_node_834_step.
 - exact (prior 833%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_835.
Lemma global_connect_835_alias v : global_word_835 v = global_word_834 v.
Proof. unfold global_word_835, global_closed_835, global_expr_835, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_835.
Lemma global_progress_835 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 8 final=Some (Gval (Fuint 1) (global_word_835 v)).
Proof.
 have Typed := types 835%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_835_step.
 - exact (prior 834%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_835_alias. apply adapt_uint_same. exact (global_size_834 v sizes).
 - exact ran.
Qed.
Lemma global_progress_836 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 17 8 final=Some (Gval (Fuint 1) (global_word_836 v)).
Proof.
 apply (global_sync_836_link invalid snapshot final v); [eapply global_progress_835; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_837 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(17 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 332 final=Some (Gval (Fuint 1) (global_word_837 v)).
Proof.
 eapply global_node_837_step.
 - exact (prior 836%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_838 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(28 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 34 final=Some (Gval (Fuint 1) (global_word_838 v)).
Proof.
 eapply global_node_838_step.
 - exact (prior 823%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (27 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_839.
Lemma global_connect_839_alias v : global_word_839 v = global_word_838 v.
Proof. unfold global_word_839, global_closed_839, global_expr_839, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_839.
Lemma global_progress_839 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(29 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 6 final=Some (Gval (Fuint 1) (global_word_839 v)).
Proof.
 have Typed := types 839%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_839_step.
 - exact (prior 838%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (28 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_839_alias. apply adapt_uint_same. exact (global_size_838 v sizes).
 - exact ran.
Qed.
Lemma global_progress_840 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(30 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::17] 11 6 final=Some (Gval (Fuint 1) (global_word_840 v)).
Proof.
 apply (global_sync_840_link invalid snapshot final v); [eapply global_progress_839; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_841 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(31 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 43 final=Some (Gval (Fuint 1) (global_word_841 v)).
Proof.
 eapply global_node_841_step.
 - exact (prior 840%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (30 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_842.
Lemma global_connect_842_alias v : global_word_842 v = global_word_841 v.
Proof. unfold global_word_842, global_closed_842, global_expr_842, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_842.
Lemma global_progress_842 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(32 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 9 final=Some (Gval (Fuint 1) (global_word_842 v)).
Proof.
 have Typed := types 842%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_842_step.
 - exact (prior 841%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (31 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_842_alias. apply adapt_uint_same. exact (global_size_841 v sizes).
 - exact ran.
Qed.
Lemma global_progress_843 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(33 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 17 9 final=Some (Gval (Fuint 1) (global_word_843 v)).
Proof.
 apply (global_sync_843_link invalid snapshot final v); [eapply global_progress_842; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_844 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(34 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 333 final=Some (Gval (Fuint 1) (global_word_844 v)).
Proof.
 eapply global_node_844_step.
 - exact (prior 843%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (33 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_845 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 18 6 final=Some (Gval (Fuint 1) (global_word_845 v)).
Proof.
 have Typed := types 845%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_845_step.
 - exact (prior 837%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_845 v sizes).
 - exact ran.
Qed.
Lemma global_progress_846 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(19 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 6 final=Some (Gval (Fuint 1) (global_word_846 v)).
Proof.
 apply (global_sync_846_link invalid snapshot final v); [eapply global_progress_845; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_847 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(20 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 40 final=Some (Gval (Fuint 1) (global_word_847 v)).
Proof.
 eapply global_node_847_step.
 - exact (prior 846%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (19 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_848 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(21 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::18] 11 4 final=Some (Gval (Fuint 1) (global_word_848 v)).
Proof.
 have Typed := types 848%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_848_step.
 - exact (prior 847%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (20 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_848 v sizes).
 - exact ran.
Qed.
Lemma global_progress_849 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(22 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 4 final=Some (Gval (Fuint 1) (global_word_849 v)).
Proof.
 apply (global_sync_849_link invalid snapshot final v); [eapply global_progress_848; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_850 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(23 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 25 final=Some (Gval (Fuint 1) (global_word_850 v)).
Proof.
 eapply global_node_850_step.
 - exact (prior 849%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (22 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_851 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 18 4 final=Some (Gval (Fuint 1) (global_word_851 v)).
Proof.
 have Typed := types 851%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_851_step.
 - exact (prior 45%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_851 v sizes).
 - exact ran.
Qed.
Lemma global_progress_852 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 4 final=Some (Gval (Fuint 1) (global_word_852 v)).
Proof.
 apply (global_sync_852_link invalid snapshot final v); [eapply global_progress_851; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_853 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::18] 10 4 final=Some (Gval (Fuint 1) (global_word_853 v)).
Proof.
 have Typed := types 853%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_853_step.
 - exact (prior 852%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_853 v sizes).
 - exact ran.
Qed.
Lemma global_progress_854 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 4 final=Some (Gval (Fuint 1) (global_word_854 v)).
Proof.
 apply (global_sync_854_link invalid snapshot final v); [eapply global_progress_853; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_855 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 25 final=Some (Gval (Fuint 1) (global_word_855 v)).
Proof.
 eapply global_node_855_step.
 - exact (prior 854%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_856 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 18 2 final=Some (Gval (Fuint 1) (global_word_856 v)).
Proof.
 have Typed := types 856%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_856_step.
 - exact (prior 43%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_856 v sizes).
 - exact ran.
Qed.
Lemma global_progress_857 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 2 final=Some (Gval (Fuint 1) (global_word_857 v)).
Proof.
 apply (global_sync_857_link invalid snapshot final v); [eapply global_progress_856; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_858 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::18] 10 2 final=Some (Gval (Fuint 1) (global_word_858 v)).
Proof.
 have Typed := types 858%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_858_step.
 - exact (prior 857%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_858 v sizes).
 - exact ran.
Qed.
Lemma global_progress_859 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 2 final=Some (Gval (Fuint 1) (global_word_859 v)).
Proof.
 apply (global_sync_859_link invalid snapshot final v); [eapply global_progress_858; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_860 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 23 final=Some (Gval (Fuint 1) (global_word_860 v)).
Proof.
 eapply global_node_860_step.
 - exact (prior 859%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_861 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 18 3 final=Some (Gval (Fuint 1) (global_word_861 v)).
Proof.
 have Typed := types 861%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_861_step.
 - exact (prior 44%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_861 v sizes).
 - exact ran.
Qed.
Lemma global_progress_862 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 3 final=Some (Gval (Fuint 1) (global_word_862 v)).
Proof.
 apply (global_sync_862_link invalid snapshot final v); [eapply global_progress_861; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_863 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::18] 10 3 final=Some (Gval (Fuint 1) (global_word_863 v)).
Proof.
 have Typed := types 863%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_863_step.
 - exact (prior 862%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_863 v sizes).
 - exact ran.
Qed.
Lemma global_progress_864 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 3 final=Some (Gval (Fuint 1) (global_word_864 v)).
Proof.
 apply (global_sync_864_link invalid snapshot final v); [eapply global_progress_863; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_865 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 24 final=Some (Gval (Fuint 1) (global_word_865 v)).
Proof.
 eapply global_node_865_step.
 - exact (prior 864%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_866 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 26 final=Some (Gval (Fuint 1) (global_word_866 v)).
Proof.
 eapply global_node_866_step.
 - exact (prior 860%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 865%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_867 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(7 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 28 final=Some (Gval (Fuint 1) (global_word_867 v)).
Proof.
 eapply global_node_867_step.
 - exact (prior 855%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 866%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_868 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 27 final=Some (Gval (Fuint 1) (global_word_868 v)).
Proof.
 eapply global_node_868_step.
 - exact (prior 860%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 865%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_869 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(7 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 29 final=Some (Gval (Fuint 1) (global_word_869 v)).
Proof.
 eapply global_node_869_step.
 - exact (prior 855%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 866%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_870 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(8 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 30 final=Some (Gval (Fuint 1) (global_word_870 v)).
Proof.
 eapply global_node_870_step.
 - exact (prior 868%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact (prior 869%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (7 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_871 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(9 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 31 final=Some (Gval (Fuint 2) (global_word_871 v)).
Proof.
 eapply global_node_871_step.
 - exact (prior 867%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (7 <= level)%coq_nat; lia))).
 - exact (prior 870%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (8 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_872 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(10 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 32 final=Some (Gval (Fuint 2) (global_word_872 v)).
Proof.
 eapply global_node_872_step.
 - exact (prior 871%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (9 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_873 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(11 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 33 final=Some (Gval (Fuint 1) (global_word_873 v)).
Proof.
 eapply global_node_873_step.
 - exact (prior 872%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (10 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_874.
Lemma global_connect_874_alias v : global_word_874 v = global_word_873 v.
Proof. unfold global_word_874, global_closed_874, global_expr_874, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_874.
Lemma global_progress_874 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(12 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 5 final=Some (Gval (Fuint 1) (global_word_874 v)).
Proof.
 have Typed := types 874%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_874_step.
 - exact (prior 873%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (11 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_874_alias. apply adapt_uint_same. exact (global_size_873 v sizes).
 - exact ran.
Qed.
Lemma global_progress_875 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::18] 10 5 final=Some (Gval (Fuint 1) (global_word_875 v)).
Proof.
 apply (global_sync_875_link invalid snapshot final v); [eapply global_progress_874; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_876 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 38 final=Some (Gval (Fuint 1) (global_word_876 v)).
Proof.
 eapply global_node_876_step.
 - exact (prior 875%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_877 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::18] 11 2 final=Some (Gval (Fuint 1) (global_word_877 v)).
Proof.
 have Typed := types 877%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_877_step.
 - exact (prior 876%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_877 v sizes).
 - exact ran.
Qed.
Lemma global_progress_878 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 2 final=Some (Gval (Fuint 1) (global_word_878 v)).
Proof.
 apply (global_sync_878_link invalid snapshot final v); [eapply global_progress_877; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_879 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(17 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 23 final=Some (Gval (Fuint 1) (global_word_879 v)).
Proof.
 eapply global_node_879_step.
 - exact (prior 878%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_880 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 18 5 final=Some (Gval (Fuint 1) (global_word_880 v)).
Proof.
 have Typed := types 880%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_880_step.
 - exact (prior 46%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_880 v sizes).
 - exact ran.
Qed.
Lemma global_progress_881 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 5 final=Some (Gval (Fuint 1) (global_word_881 v)).
Proof.
 apply (global_sync_881_link invalid snapshot final v); [eapply global_progress_880; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_882 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 39 final=Some (Gval (Fuint 1) (global_word_882 v)).
Proof.
 eapply global_node_882_step.
 - exact (prior 881%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_883 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::18] 11 3 final=Some (Gval (Fuint 1) (global_word_883 v)).
Proof.
 have Typed := types 883%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_883_step.
 - exact (prior 882%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_883 v sizes).
 - exact ran.
Qed.
Lemma global_progress_884 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 3 final=Some (Gval (Fuint 1) (global_word_884 v)).
Proof.
 apply (global_sync_884_link invalid snapshot final v); [eapply global_progress_883; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_885 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 24 final=Some (Gval (Fuint 1) (global_word_885 v)).
Proof.
 eapply global_node_885_step.
 - exact (prior 884%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_886 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 26 final=Some (Gval (Fuint 1) (global_word_886 v)).
Proof.
 eapply global_node_886_step.
 - exact (prior 879%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact (prior 885%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_887 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(24 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 28 final=Some (Gval (Fuint 1) (global_word_887 v)).
Proof.
 eapply global_node_887_step.
 - exact (prior 850%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (23 <= level)%coq_nat; lia))).
 - exact (prior 886%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_888 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 27 final=Some (Gval (Fuint 1) (global_word_888 v)).
Proof.
 eapply global_node_888_step.
 - exact (prior 879%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact (prior 885%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_889 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(24 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 29 final=Some (Gval (Fuint 1) (global_word_889 v)).
Proof.
 eapply global_node_889_step.
 - exact (prior 850%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (23 <= level)%coq_nat; lia))).
 - exact (prior 886%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_890 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(25 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 30 final=Some (Gval (Fuint 1) (global_word_890 v)).
Proof.
 eapply global_node_890_step.
 - exact (prior 888%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact (prior 889%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (24 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_891 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(26 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 31 final=Some (Gval (Fuint 2) (global_word_891 v)).
Proof.
 eapply global_node_891_step.
 - exact (prior 887%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (24 <= level)%coq_nat; lia))).
 - exact (prior 890%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (25 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_892 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(27 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 32 final=Some (Gval (Fuint 2) (global_word_892 v)).
Proof.
 eapply global_node_892_step.
 - exact (prior 891%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (26 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_893 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(28 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 33 final=Some (Gval (Fuint 1) (global_word_893 v)).
Proof.
 eapply global_node_893_step.
 - exact (prior 892%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (27 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_894.
Lemma global_connect_894_alias v : global_word_894 v = global_word_893 v.
Proof. unfold global_word_894, global_closed_894, global_expr_894, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_894.
Lemma global_progress_894 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(29 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 5 final=Some (Gval (Fuint 1) (global_word_894 v)).
Proof.
 have Typed := types 894%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_894_step.
 - exact (prior 893%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (28 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_894_alias. apply adapt_uint_same. exact (global_size_893 v sizes).
 - exact ran.
Qed.
Lemma global_progress_895 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(30 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::18] 11 5 final=Some (Gval (Fuint 1) (global_word_895 v)).
Proof.
 apply (global_sync_895_link invalid snapshot final v); [eapply global_progress_894; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_896 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(31 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 41 final=Some (Gval (Fuint 1) (global_word_896 v)).
Proof.
 eapply global_node_896_step.
 - exact (prior 895%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (30 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_897.
Lemma global_connect_897_alias v : global_word_897 v = global_word_896 v.
Proof. unfold global_word_897, global_closed_897, global_expr_897, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_897.
Lemma global_progress_897 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(32 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 7 final=Some (Gval (Fuint 1) (global_word_897 v)).
Proof.
 have Typed := types 897%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_897_step.
 - exact (prior 896%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (31 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_897_alias. apply adapt_uint_same. exact (global_size_896 v sizes).
 - exact ran.
Qed.
Lemma global_progress_898 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(33 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 18 7 final=Some (Gval (Fuint 1) (global_word_898 v)).
Proof.
 apply (global_sync_898_link invalid snapshot final v); [eapply global_progress_897; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_899 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(34 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 334 final=Some (Gval (Fuint 1) (global_word_899 v)).
Proof.
 eapply global_node_899_step.
 - exact (prior 898%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (33 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_900 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(11 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 34 final=Some (Gval (Fuint 1) (global_word_900 v)).
Proof.
 eapply global_node_900_step.
 - exact (prior 872%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (10 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_901.
Lemma global_connect_901_alias v : global_word_901 v = global_word_900 v.
Proof. unfold global_word_901, global_closed_901, global_expr_901, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_901.
Lemma global_progress_901 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(12 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 6 final=Some (Gval (Fuint 1) (global_word_901 v)).
Proof.
 have Typed := types 901%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_901_step.
 - exact (prior 900%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (11 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_901_alias. apply adapt_uint_same. exact (global_size_900 v sizes).
 - exact ran.
Qed.
Lemma global_progress_902 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::18] 10 6 final=Some (Gval (Fuint 1) (global_word_902 v)).
Proof.
 apply (global_sync_902_link invalid snapshot final v); [eapply global_progress_901; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_903 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 42 final=Some (Gval (Fuint 1) (global_word_903 v)).
Proof.
 eapply global_node_903_step.
 - exact (prior 902%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_904.
Lemma global_connect_904_alias v : global_word_904 v = global_word_903 v.
Proof. unfold global_word_904, global_closed_904, global_expr_904, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_904.
Lemma global_progress_904 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 8 final=Some (Gval (Fuint 1) (global_word_904 v)).
Proof.
 have Typed := types 904%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_904_step.
 - exact (prior 903%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_904_alias. apply adapt_uint_same. exact (global_size_903 v sizes).
 - exact ran.
Qed.
Lemma global_progress_905 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 18 8 final=Some (Gval (Fuint 1) (global_word_905 v)).
Proof.
 apply (global_sync_905_link invalid snapshot final v); [eapply global_progress_904; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_906 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(17 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 335 final=Some (Gval (Fuint 1) (global_word_906 v)).
Proof.
 eapply global_node_906_step.
 - exact (prior 905%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_907 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(28 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 34 final=Some (Gval (Fuint 1) (global_word_907 v)).
Proof.
 eapply global_node_907_step.
 - exact (prior 892%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (27 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_908.
Lemma global_connect_908_alias v : global_word_908 v = global_word_907 v.
Proof. unfold global_word_908, global_closed_908, global_expr_908, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_908.
Lemma global_progress_908 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(29 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 6 final=Some (Gval (Fuint 1) (global_word_908 v)).
Proof.
 have Typed := types 908%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_908_step.
 - exact (prior 907%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (28 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_908_alias. apply adapt_uint_same. exact (global_size_907 v sizes).
 - exact ran.
Qed.
Lemma global_progress_909 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(30 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::18] 11 6 final=Some (Gval (Fuint 1) (global_word_909 v)).
Proof.
 apply (global_sync_909_link invalid snapshot final v); [eapply global_progress_908; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_910 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(31 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 43 final=Some (Gval (Fuint 1) (global_word_910 v)).
Proof.
 eapply global_node_910_step.
 - exact (prior 909%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (30 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_911.
Lemma global_connect_911_alias v : global_word_911 v = global_word_910 v.
Proof. unfold global_word_911, global_closed_911, global_expr_911, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_911.
Lemma global_progress_911 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(32 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 9 final=Some (Gval (Fuint 1) (global_word_911 v)).
Proof.
 have Typed := types 911%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_911_step.
 - exact (prior 910%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (31 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_911_alias. apply adapt_uint_same. exact (global_size_910 v sizes).
 - exact ran.
Qed.
Lemma global_progress_912 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(33 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 18 9 final=Some (Gval (Fuint 1) (global_word_912 v)).
Proof.
 apply (global_sync_912_link invalid snapshot final v); [eapply global_progress_911; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_913 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(34 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 336 final=Some (Gval (Fuint 1) (global_word_913 v)).
Proof.
 eapply global_node_913_step.
 - exact (prior 912%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (33 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_914 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 19 4 final=Some (Gval (Fuint 1) (global_word_914 v)).
Proof.
 have Typed := types 914%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_914_step.
 - exact (prior 49%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_914 v sizes).
 - exact ran.
Qed.
Lemma global_progress_915 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 4 final=Some (Gval (Fuint 1) (global_word_915 v)).
Proof.
 apply (global_sync_915_link invalid snapshot final v); [eapply global_progress_914; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_916 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 25 final=Some (Gval (Fuint 1) (global_word_916 v)).
Proof.
 eapply global_node_916_step.
 - exact (prior 915%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_917 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 19 2 final=Some (Gval (Fuint 1) (global_word_917 v)).
Proof.
 have Typed := types 917%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_917_step.
 - exact (prior 47%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_917 v sizes).
 - exact ran.
Qed.
Lemma global_progress_918 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 2 final=Some (Gval (Fuint 1) (global_word_918 v)).
Proof.
 apply (global_sync_918_link invalid snapshot final v); [eapply global_progress_917; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_919 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 23 final=Some (Gval (Fuint 1) (global_word_919 v)).
Proof.
 eapply global_node_919_step.
 - exact (prior 918%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_920 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 19 3 final=Some (Gval (Fuint 1) (global_word_920 v)).
Proof.
 have Typed := types 920%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_920_step.
 - exact (prior 48%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_920 v sizes).
 - exact ran.
Qed.
Lemma global_progress_921 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 3 final=Some (Gval (Fuint 1) (global_word_921 v)).
Proof.
 apply (global_sync_921_link invalid snapshot final v); [eapply global_progress_920; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_922 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 24 final=Some (Gval (Fuint 1) (global_word_922 v)).
Proof.
 eapply global_node_922_step.
 - exact (prior 921%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_923 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 26 final=Some (Gval (Fuint 1) (global_word_923 v)).
Proof.
 eapply global_node_923_step.
 - exact (prior 919%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact (prior 922%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_924 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 28 final=Some (Gval (Fuint 1) (global_word_924 v)).
Proof.
 eapply global_node_924_step.
 - exact (prior 916%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact (prior 923%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_925 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 27 final=Some (Gval (Fuint 1) (global_word_925 v)).
Proof.
 eapply global_node_925_step.
 - exact (prior 919%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact (prior 922%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_926 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 29 final=Some (Gval (Fuint 1) (global_word_926 v)).
Proof.
 eapply global_node_926_step.
 - exact (prior 916%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact (prior 923%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_927 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 30 final=Some (Gval (Fuint 1) (global_word_927 v)).
Proof.
 eapply global_node_927_step.
 - exact (prior 925%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact (prior 926%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_928 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(7 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 31 final=Some (Gval (Fuint 2) (global_word_928 v)).
Proof.
 eapply global_node_928_step.
 - exact (prior 924%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 927%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_929 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(8 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 32 final=Some (Gval (Fuint 2) (global_word_929 v)).
Proof.
 eapply global_node_929_step.
 - exact (prior 928%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (7 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_930 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(9 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 33 final=Some (Gval (Fuint 1) (global_word_930 v)).
Proof.
 eapply global_node_930_step.
 - exact (prior 929%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (8 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_931.
Lemma global_connect_931_alias v : global_word_931 v = global_word_930 v.
Proof. unfold global_word_931, global_closed_931, global_expr_931, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_931.
Lemma global_progress_931 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(10 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 5 final=Some (Gval (Fuint 1) (global_word_931 v)).
Proof.
 have Typed := types 931%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_931_step.
 - exact (prior 930%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (9 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_931_alias. apply adapt_uint_same. exact (global_size_930 v sizes).
 - exact ran.
Qed.
Lemma global_progress_932 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(11 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 19 5 final=Some (Gval (Fuint 1) (global_word_932 v)).
Proof.
 apply (global_sync_932_link invalid snapshot final v); [eapply global_progress_931; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_933 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(12 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 337 final=Some (Gval (Fuint 1) (global_word_933 v)).
Proof.
 eapply global_node_933_step.
 - exact (prior 932%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (11 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_934 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(9 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 34 final=Some (Gval (Fuint 1) (global_word_934 v)).
Proof.
 eapply global_node_934_step.
 - exact (prior 929%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (8 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_935.
Lemma global_connect_935_alias v : global_word_935 v = global_word_934 v.
Proof. unfold global_word_935, global_closed_935, global_expr_935, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_935.
Lemma global_progress_935 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(10 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 6 final=Some (Gval (Fuint 1) (global_word_935 v)).
Proof.
 have Typed := types 935%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_935_step.
 - exact (prior 934%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (9 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_935_alias. apply adapt_uint_same. exact (global_size_934 v sizes).
 - exact ran.
Qed.
Lemma global_progress_936 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(11 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 19 6 final=Some (Gval (Fuint 1) (global_word_936 v)).
Proof.
 apply (global_sync_936_link invalid snapshot final v); [eapply global_progress_935; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_937 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(12 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 338 final=Some (Gval (Fuint 1) (global_word_937 v)).
Proof.
 eapply global_node_937_step.
 - exact (prior 936%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (11 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_938 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 20 2 final=Some (Gval (Fuint 1) (global_word_938 v)).
Proof.
 have Typed := types 938%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_938_step.
 - exact (prior 50%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_938 v sizes).
 - exact ran.
Qed.
Lemma global_progress_939 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::20] 2 final=Some (Gval (Fuint 1) (global_word_939 v)).
Proof.
 apply (global_sync_939_link invalid snapshot final v); [eapply global_progress_938; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_940 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::20] 19 final=Some (Gval (Fuint 1) (global_word_940 v)).
Proof.
 eapply global_node_940_step.
 - exact (prior 939%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_941 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 20 3 final=Some (Gval (Fuint 1) (global_word_941 v)).
Proof.
 have Typed := types 941%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_941_step.
 - exact (prior 51%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_941 v sizes).
 - exact ran.
Qed.
Lemma global_progress_942 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::20] 3 final=Some (Gval (Fuint 1) (global_word_942 v)).
Proof.
 apply (global_sync_942_link invalid snapshot final v); [eapply global_progress_941; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_943 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::20] 20 final=Some (Gval (Fuint 1) (global_word_943 v)).
Proof.
 eapply global_node_943_step.
 - exact (prior 942%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_944 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::20] 21 final=Some (Gval (Fuint 1) (global_word_944 v)).
Proof.
 eapply global_node_944_step.
 - exact (prior 940%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact (prior 943%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_945 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::20] 22 final=Some (Gval (Fuint 1) (global_word_945 v)).
Proof.
 eapply global_node_945_step.
 - exact (prior 940%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact (prior 943%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_946 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::20] 23 final=Some (Gval (Fuint 2) (global_word_946 v)).
Proof.
 eapply global_node_946_step.
 - exact (prior 944%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact (prior 945%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_947 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::20] 24 final=Some (Gval (Fuint 2) (global_word_947 v)).
Proof.
 eapply global_node_947_step.
 - exact (prior 946%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_948 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(7 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::20] 25 final=Some (Gval (Fuint 1) (global_word_948 v)).
Proof.
 eapply global_node_948_step.
 - exact (prior 947%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_949.
Lemma global_connect_949_alias v : global_word_949 v = global_word_948 v.
Proof. unfold global_word_949, global_closed_949, global_expr_949, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_949.
Lemma global_progress_949 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(8 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::20] 4 final=Some (Gval (Fuint 1) (global_word_949 v)).
Proof.
 have Typed := types 949%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_949_step.
 - exact (prior 948%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (7 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_949_alias. apply adapt_uint_same. exact (global_size_948 v sizes).
 - exact ran.
Qed.
Lemma global_progress_950 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(9 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 20 4 final=Some (Gval (Fuint 1) (global_word_950 v)).
Proof.
 apply (global_sync_950_link invalid snapshot final v); [eapply global_progress_949; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_951 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(10 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 339 final=Some (Gval (Fuint 1) (global_word_951 v)).
Proof.
 eapply global_node_951_step.
 - exact (prior 950%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (9 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_952 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(7 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::20] 26 final=Some (Gval (Fuint 1) (global_word_952 v)).
Proof.
 eapply global_node_952_step.
 - exact (prior 947%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_953.
Lemma global_connect_953_alias v : global_word_953 v = global_word_952 v.
Proof. unfold global_word_953, global_closed_953, global_expr_953, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_953.
Lemma global_progress_953 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(8 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::20] 5 final=Some (Gval (Fuint 1) (global_word_953 v)).
Proof.
 have Typed := types 953%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_953_step.
 - exact (prior 952%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (7 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_953_alias. apply adapt_uint_same. exact (global_size_952 v sizes).
 - exact ran.
Qed.
Lemma global_progress_954 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(9 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 20 5 final=Some (Gval (Fuint 1) (global_word_954 v)).
Proof.
 apply (global_sync_954_link invalid snapshot final v); [eapply global_progress_953; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_955 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(10 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 340 final=Some (Gval (Fuint 1) (global_word_955 v)).
Proof.
 eapply global_node_955_step.
 - exact (prior 954%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (9 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_956 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 21 2 final=Some (Gval (Fuint 1) (global_word_956 v)).
Proof.
 have Typed := types 956%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_956_step.
 - exact (prior 52%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_956 v sizes).
 - exact ran.
Qed.
Lemma global_progress_957 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::21] 2 final=Some (Gval (Fuint 1) (global_word_957 v)).
Proof.
 apply (global_sync_957_link invalid snapshot final v); [eapply global_progress_956; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_958 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::21] 19 final=Some (Gval (Fuint 1) (global_word_958 v)).
Proof.
 eapply global_node_958_step.
 - exact (prior 957%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_959 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 21 3 final=Some (Gval (Fuint 1) (global_word_959 v)).
Proof.
 have Typed := types 959%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_959_step.
 - exact (prior 54%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_959 v sizes).
 - exact ran.
Qed.
Lemma global_progress_960 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::21] 3 final=Some (Gval (Fuint 1) (global_word_960 v)).
Proof.
 apply (global_sync_960_link invalid snapshot final v); [eapply global_progress_959; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_961 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::21] 20 final=Some (Gval (Fuint 1) (global_word_961 v)).
Proof.
 eapply global_node_961_step.
 - exact (prior 960%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_962 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::21] 21 final=Some (Gval (Fuint 1) (global_word_962 v)).
Proof.
 eapply global_node_962_step.
 - exact (prior 958%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact (prior 961%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_963 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::21] 22 final=Some (Gval (Fuint 1) (global_word_963 v)).
Proof.
 eapply global_node_963_step.
 - exact (prior 958%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact (prior 961%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_964 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::21] 23 final=Some (Gval (Fuint 2) (global_word_964 v)).
Proof.
 eapply global_node_964_step.
 - exact (prior 962%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact (prior 963%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_965 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::21] 24 final=Some (Gval (Fuint 2) (global_word_965 v)).
Proof.
 eapply global_node_965_step.
 - exact (prior 964%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_966 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(7 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::21] 25 final=Some (Gval (Fuint 1) (global_word_966 v)).
Proof.
 eapply global_node_966_step.
 - exact (prior 965%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_967.
Lemma global_connect_967_alias v : global_word_967 v = global_word_966 v.
Proof. unfold global_word_967, global_closed_967, global_expr_967, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_967.
Lemma global_progress_967 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(8 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::21] 4 final=Some (Gval (Fuint 1) (global_word_967 v)).
Proof.
 have Typed := types 967%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_967_step.
 - exact (prior 966%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (7 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_967_alias. apply adapt_uint_same. exact (global_size_966 v sizes).
 - exact ran.
Qed.
Lemma global_progress_968 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(9 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 21 4 final=Some (Gval (Fuint 1) (global_word_968 v)).
Proof.
 apply (global_sync_968_link invalid snapshot final v); [eapply global_progress_967; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_969 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(10 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 341 final=Some (Gval (Fuint 1) (global_word_969 v)).
Proof.
 eapply global_node_969_step.
 - exact (prior 968%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (9 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_970 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(7 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::21] 26 final=Some (Gval (Fuint 1) (global_word_970 v)).
Proof.
 eapply global_node_970_step.
 - exact (prior 965%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_971.
Lemma global_connect_971_alias v : global_word_971 v = global_word_970 v.
Proof. unfold global_word_971, global_closed_971, global_expr_971, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_971.
Lemma global_progress_971 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(8 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::21] 5 final=Some (Gval (Fuint 1) (global_word_971 v)).
Proof.
 have Typed := types 971%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_971_step.
 - exact (prior 970%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (7 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_971_alias. apply adapt_uint_same. exact (global_size_970 v sizes).
 - exact ran.
Qed.
Lemma global_progress_972 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(9 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 21 5 final=Some (Gval (Fuint 1) (global_word_972 v)).
Proof.
 apply (global_sync_972_link invalid snapshot final v); [eapply global_progress_971; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_973 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(10 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 342 final=Some (Gval (Fuint 1) (global_word_973 v)).
Proof.
 eapply global_node_973_step.
 - exact (prior 972%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (9 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_974 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(11 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 22 2 final=Some (Gval (Fuint 1) (global_word_974 v)).
Proof.
 have Typed := types 974%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_974_step.
 - exact (prior 309%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (10 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_974 v sizes).
 - exact ran.
Qed.
Lemma global_progress_975 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(12 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::22] 2 final=Some (Gval (Fuint 1) (global_word_975 v)).
Proof.
 apply (global_sync_975_link invalid snapshot final v); [eapply global_progress_974; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_976 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::22] 19 final=Some (Gval (Fuint 1) (global_word_976 v)).
Proof.
 eapply global_node_976_step.
 - exact (prior 975%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (12 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_977 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(11 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 22 3 final=Some (Gval (Fuint 1) (global_word_977 v)).
Proof.
 have Typed := types 977%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_977_step.
 - exact (prior 295%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (10 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_977 v sizes).
 - exact ran.
Qed.
Lemma global_progress_978 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(12 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::22] 3 final=Some (Gval (Fuint 1) (global_word_978 v)).
Proof.
 apply (global_sync_978_link invalid snapshot final v); [eapply global_progress_977; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_979 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::22] 20 final=Some (Gval (Fuint 1) (global_word_979 v)).
Proof.
 eapply global_node_979_step.
 - exact (prior 978%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (12 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_980 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::22] 21 final=Some (Gval (Fuint 1) (global_word_980 v)).
Proof.
 eapply global_node_980_step.
 - exact (prior 976%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact (prior 979%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_981 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::22] 22 final=Some (Gval (Fuint 1) (global_word_981 v)).
Proof.
 eapply global_node_981_step.
 - exact (prior 976%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact (prior 979%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_982 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::22] 23 final=Some (Gval (Fuint 2) (global_word_982 v)).
Proof.
 eapply global_node_982_step.
 - exact (prior 980%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact (prior 981%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_983 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::22] 24 final=Some (Gval (Fuint 2) (global_word_983 v)).
Proof.
 eapply global_node_983_step.
 - exact (prior 982%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_984 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(17 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::22] 25 final=Some (Gval (Fuint 1) (global_word_984 v)).
Proof.
 eapply global_node_984_step.
 - exact (prior 983%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_985.
Lemma global_connect_985_alias v : global_word_985 v = global_word_984 v.
Proof. unfold global_word_985, global_closed_985, global_expr_985, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_985.
Lemma global_progress_985 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::22] 4 final=Some (Gval (Fuint 1) (global_word_985 v)).
Proof.
 have Typed := types 985%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_985_step.
 - exact (prior 984%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_985_alias. apply adapt_uint_same. exact (global_size_984 v sizes).
 - exact ran.
Qed.
Lemma global_progress_986 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(19 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 22 4 final=Some (Gval (Fuint 1) (global_word_986 v)).
Proof.
 apply (global_sync_986_link invalid snapshot final v); [eapply global_progress_985; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_987 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(20 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 343 final=Some (Gval (Fuint 1) (global_word_987 v)).
Proof.
 eapply global_node_987_step.
 - exact (prior 986%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (19 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_988 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(17 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::22] 26 final=Some (Gval (Fuint 1) (global_word_988 v)).
Proof.
 eapply global_node_988_step.
 - exact (prior 983%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_989.
Lemma global_connect_989_alias v : global_word_989 v = global_word_988 v.
Proof. unfold global_word_989, global_closed_989, global_expr_989, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_989.
Lemma global_progress_989 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::22] 5 final=Some (Gval (Fuint 1) (global_word_989 v)).
Proof.
 have Typed := types 989%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_989_step.
 - exact (prior 988%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_989_alias. apply adapt_uint_same. exact (global_size_988 v sizes).
 - exact ran.
Qed.
Lemma global_progress_990 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(19 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 22 5 final=Some (Gval (Fuint 1) (global_word_990 v)).
Proof.
 apply (global_sync_990_link invalid snapshot final v); [eapply global_progress_989; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_991 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(20 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 344 final=Some (Gval (Fuint 1) (global_word_991 v)).
Proof.
 eapply global_node_991_step.
 - exact (prior 990%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (19 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_992 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 23 2 final=Some (Gval (Fuint 1) (global_word_992 v)).
Proof.
 have Typed := types 992%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_992_step.
 - exact (prior 333%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (12 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_992 v sizes).
 - exact ran.
Qed.
Lemma global_progress_993 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::23] 2 final=Some (Gval (Fuint 1) (global_word_993 v)).
Proof.
 apply (global_sync_993_link invalid snapshot final v); [eapply global_progress_992; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_994 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::23] 19 final=Some (Gval (Fuint 1) (global_word_994 v)).
Proof.
 eapply global_node_994_step.
 - exact (prior 993%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_995 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(11 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 23 3 final=Some (Gval (Fuint 1) (global_word_995 v)).
Proof.
 have Typed := types 995%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_995_step.
 - exact (prior 313%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (10 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_995 v sizes).
 - exact ran.
Qed.
Lemma global_progress_996 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(12 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::23] 3 final=Some (Gval (Fuint 1) (global_word_996 v)).
Proof.
 apply (global_sync_996_link invalid snapshot final v); [eapply global_progress_995; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_997 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::23] 20 final=Some (Gval (Fuint 1) (global_word_997 v)).
Proof.
 eapply global_node_997_step.
 - exact (prior 996%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (12 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_998 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::23] 21 final=Some (Gval (Fuint 1) (global_word_998 v)).
Proof.
 eapply global_node_998_step.
 - exact (prior 994%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 997%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_999 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::23] 22 final=Some (Gval (Fuint 1) (global_word_999 v)).
Proof.
 eapply global_node_999_step.
 - exact (prior 994%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 997%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
