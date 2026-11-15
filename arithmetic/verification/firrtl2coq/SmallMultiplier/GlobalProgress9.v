From Coq Require Import NArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import HierarchyFacts PortFieldFacts.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalWidthFacts GlobalNodeSteps GlobalFieldSteps GlobalScalarSteps GlobalSyncSteps GlobalLeaves.
Local Open Scope N_scope.
From SmallMultiplier Require Import GlobalProgressTypes.
From SmallMultiplier Require Export GlobalProgress8.
Lemma global_progress_1800 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::16] 35 final=Some (Gval (Fuint 1) (global_word_1800 v)).
Proof.
 eapply global_node_1800_step.
 - exact (prior 1799%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1801 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::16] 36 final=Some (Gval (Fuint 1) (global_word_1801 v)).
Proof.
 eapply global_node_1801_step.
 - exact (prior 1800%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1802 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(39 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::16] 37 final=Some (Gval (Fuint 1) (global_word_1802 v)).
Proof.
 eapply global_node_1802_step.
 - exact (prior 1798%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (38 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1803 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::16] 0 final=Some (Gval Fclock (global_word_1803 v)).
Proof.
 apply (global_sync_1803_link invalid snapshot final v); [eapply global_progress_1328; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1804 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::16] 10 0 final=Some (Gval Fclock (global_word_1804 v)).
Proof.
 have Typed := types 1804%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1804_step.
 - exact (prior 1803%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - reflexivity.
 - exact ran.
Qed.
Lemma global_progress_1805 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::16] 10 1 final=Some (Gval (Fuint 1) (global_word_1805 v)).
Proof.
 have Typed := types 1805%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1805_step.
 - exact (prior 1799%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1805 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1806 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::16] 11 0 final=Some (Gval Fclock (global_word_1806 v)).
Proof.
 have Typed := types 1806%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1806_step.
 - exact (prior 1803%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - reflexivity.
 - exact ran.
Qed.
Lemma global_progress_1807 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::16] 11 1 final=Some (Gval (Fuint 1) (global_word_1807 v)).
Proof.
 have Typed := types 1807%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1807_step.
 - exact (prior 1799%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1807 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1808 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 7 final=Some (Gval (Fuint 4) (global_word_1808 v)).
Proof.
 eapply global_node_1808_step.
 - exact (prior 721%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1809 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 8 final=Some (Gval (Fuint 4) (global_word_1809 v)).
Proof.
 eapply global_node_1809_step.
 - exact (prior 726%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1810 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 9 final=Some (Gval (Fuint 4) (global_word_1810 v)).
Proof.
 eapply global_node_1810_step.
 - exact (prior 716%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1811 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 10 final=Some (Gval (Fuint 5) (global_word_1811 v)).
Proof.
 eapply global_node_1811_step.
 - exact (prior 1808%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 1809%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1812 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(7 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 11 final=Some (Gval (Fuint 4) (global_word_1812 v)).
Proof.
 eapply global_node_1812_step.
 - exact (prior 1811%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1813 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(8 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 12 final=Some (Gval (Fuint 5) (global_word_1813 v)).
Proof.
 eapply global_node_1813_step.
 - exact (prior 1812%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (7 <= level)%coq_nat; lia))).
 - exact (prior 1810%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1814 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(9 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 13 final=Some (Gval (Fuint 4) (global_word_1814 v)).
Proof.
 eapply global_node_1814_step.
 - exact (prior 1813%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (8 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1815 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 14 final=Some (Gval (Fuint 4) (global_word_1815 v)).
Proof.
 eapply global_node_1815_step.
 - exact (prior 736%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (12 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1816 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 15 final=Some (Gval (Fuint 4) (global_word_1816 v)).
Proof.
 eapply global_node_1816_step.
 - exact (prior 763%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (12 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1817 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 16 final=Some (Gval (Fuint 5) (global_word_1817 v)).
Proof.
 eapply global_node_1817_step.
 - exact (prior 1816%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1818 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 17 final=Some (Gval (Fuint 6) (global_word_1818 v)).
Proof.
 eapply global_node_1818_step.
 - exact (prior 1815%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact (prior 1817%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1819 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 18 final=Some (Gval (Fuint 5) (global_word_1819 v)).
Proof.
 eapply global_node_1819_step.
 - exact (prior 1818%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1820 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(17 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 19 final=Some (Gval (Fuint 1) (global_word_1820 v)).
Proof.
 eapply global_node_1820_step.
 - exact (prior 1814%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (9 <= level)%coq_nat; lia))).
 - exact (prior 1819%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1821 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 1 final=Some (Gval (Fuint 1) (global_word_1821 v)).
Proof.
 apply (global_sync_1821_link invalid snapshot final v); [eapply global_progress_1805; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1822 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 20 final=Some (Gval (Fuint 1) (global_word_1822 v)).
Proof.
 eapply global_node_1822_step.
 - exact (prior 1821%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1823 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 21 final=Some (Gval (Fuint 1) (global_word_1823 v)).
Proof.
 eapply global_node_1823_step.
 - exact (prior 1822%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1824 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 22 final=Some (Gval (Fuint 1) (global_word_1824 v)).
Proof.
 eapply global_node_1824_step.
 - exact (prior 1820%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1825 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 0 final=Some (Gval Fclock (global_word_1825 v)).
Proof.
 apply (global_sync_1825_link invalid snapshot final v); [eapply global_progress_1804; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1826 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(17 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 7 final=Some (Gval (Fuint 4) (global_word_1826 v)).
Proof.
 eapply global_node_1826_step.
 - exact (prior 740%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1827 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 8 final=Some (Gval (Fuint 4) (global_word_1827 v)).
Proof.
 eapply global_node_1827_step.
 - exact (prior 746%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1828 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(23 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 9 final=Some (Gval (Fuint 4) (global_word_1828 v)).
Proof.
 eapply global_node_1828_step.
 - exact (prior 711%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (22 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1829 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 10 final=Some (Gval (Fuint 5) (global_word_1829 v)).
Proof.
 eapply global_node_1829_step.
 - exact (prior 1826%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact (prior 1827%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1830 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(19 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 11 final=Some (Gval (Fuint 4) (global_word_1830 v)).
Proof.
 eapply global_node_1830_step.
 - exact (prior 1829%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1831 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(24 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 12 final=Some (Gval (Fuint 5) (global_word_1831 v)).
Proof.
 eapply global_node_1831_step.
 - exact (prior 1830%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (19 <= level)%coq_nat; lia))).
 - exact (prior 1828%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (23 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1832 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(25 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 13 final=Some (Gval (Fuint 4) (global_word_1832 v)).
Proof.
 eapply global_node_1832_step.
 - exact (prior 1831%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (24 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1833 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(30 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 14 final=Some (Gval (Fuint 4) (global_word_1833 v)).
Proof.
 eapply global_node_1833_step.
 - exact (prior 756%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (29 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1834 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(30 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 15 final=Some (Gval (Fuint 4) (global_word_1834 v)).
Proof.
 eapply global_node_1834_step.
 - exact (prior 770%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (29 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1835 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(31 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 16 final=Some (Gval (Fuint 5) (global_word_1835 v)).
Proof.
 eapply global_node_1835_step.
 - exact (prior 1834%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (30 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1836 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(32 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 17 final=Some (Gval (Fuint 6) (global_word_1836 v)).
Proof.
 eapply global_node_1836_step.
 - exact (prior 1833%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (30 <= level)%coq_nat; lia))).
 - exact (prior 1835%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (31 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1837 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(33 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 18 final=Some (Gval (Fuint 5) (global_word_1837 v)).
Proof.
 eapply global_node_1837_step.
 - exact (prior 1836%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (32 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1838 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(34 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 19 final=Some (Gval (Fuint 1) (global_word_1838 v)).
Proof.
 eapply global_node_1838_step.
 - exact (prior 1832%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (25 <= level)%coq_nat; lia))).
 - exact (prior 1837%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (33 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1839 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 1 final=Some (Gval (Fuint 1) (global_word_1839 v)).
Proof.
 apply (global_sync_1839_link invalid snapshot final v); [eapply global_progress_1807; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1840 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 20 final=Some (Gval (Fuint 1) (global_word_1840 v)).
Proof.
 eapply global_node_1840_step.
 - exact (prior 1839%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1841 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 21 final=Some (Gval (Fuint 1) (global_word_1841 v)).
Proof.
 eapply global_node_1841_step.
 - exact (prior 1840%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1842 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(35 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 22 final=Some (Gval (Fuint 1) (global_word_1842 v)).
Proof.
 eapply global_node_1842_step.
 - exact (prior 1838%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (34 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1843 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 0 final=Some (Gval Fclock (global_word_1843 v)).
Proof.
 apply (global_sync_1843_link invalid snapshot final v); [eapply global_progress_1806; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1844 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 12 final=Some (Gval (Fuint 4) (global_word_1844 v)).
Proof.
 eapply global_node_1844_step.
 - exact (prior 788%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1845 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 13 final=Some (Gval (Fuint 4) (global_word_1845 v)).
Proof.
 eapply global_node_1845_step.
 - exact (prior 793%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1846 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 14 final=Some (Gval (Fuint 4) (global_word_1846 v)).
Proof.
 eapply global_node_1846_step.
 - exact (prior 783%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1847 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 15 final=Some (Gval (Fuint 4) (global_word_1847 v)).
Proof.
 eapply global_node_1847_step.
 - exact (prior 812%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1848 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(20 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 16 final=Some (Gval (Fuint 4) (global_word_1848 v)).
Proof.
 eapply global_node_1848_step.
 - exact (prior 777%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (19 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1849 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 17 final=Some (Gval (Fuint 5) (global_word_1849 v)).
Proof.
 eapply global_node_1849_step.
 - exact (prior 1844%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact (prior 1845%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1850 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 18 final=Some (Gval (Fuint 4) (global_word_1850 v)).
Proof.
 eapply global_node_1850_step.
 - exact (prior 1849%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1851 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 19 final=Some (Gval (Fuint 5) (global_word_1851 v)).
Proof.
 eapply global_node_1851_step.
 - exact (prior 1846%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact (prior 1850%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1852 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(7 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 20 final=Some (Gval (Fuint 4) (global_word_1852 v)).
Proof.
 eapply global_node_1852_step.
 - exact (prior 1851%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1853 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(8 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 21 final=Some (Gval (Fuint 5) (global_word_1853 v)).
Proof.
 eapply global_node_1853_step.
 - exact (prior 1847%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact (prior 1852%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (7 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1854 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(9 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 22 final=Some (Gval (Fuint 4) (global_word_1854 v)).
Proof.
 eapply global_node_1854_step.
 - exact (prior 1853%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (8 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1855 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(21 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 23 final=Some (Gval (Fuint 5) (global_word_1855 v)).
Proof.
 eapply global_node_1855_step.
 - exact (prior 1848%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (20 <= level)%coq_nat; lia))).
 - exact (prior 1854%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (9 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1856 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(22 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 24 final=Some (Gval (Fuint 4) (global_word_1856 v)).
Proof.
 eapply global_node_1856_step.
 - exact (prior 1855%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (21 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1857 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(33 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 25 final=Some (Gval (Fuint 4) (global_word_1857 v)).
Proof.
 eapply global_node_1857_step.
 - exact (prior 828%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (32 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1858 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 26 final=Some (Gval (Fuint 4) (global_word_1858 v)).
Proof.
 eapply global_node_1858_step.
 - exact (prior 835%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1859 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(17 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 27 final=Some (Gval (Fuint 5) (global_word_1859 v)).
Proof.
 eapply global_node_1859_step.
 - exact (prior 1858%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1860 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(33 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 28 final=Some (Gval (Fuint 4) (global_word_1860 v)).
Proof.
 eapply global_node_1860_step.
 - exact (prior 842%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (32 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1861 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(34 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 29 final=Some (Gval (Fuint 5) (global_word_1861 v)).
Proof.
 eapply global_node_1861_step.
 - exact (prior 1860%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (33 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1862 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(34 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 30 final=Some (Gval (Fuint 6) (global_word_1862 v)).
Proof.
 eapply global_node_1862_step.
 - exact (prior 1857%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (33 <= level)%coq_nat; lia))).
 - exact (prior 1859%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1863 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(35 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 31 final=Some (Gval (Fuint 5) (global_word_1863 v)).
Proof.
 eapply global_node_1863_step.
 - exact (prior 1862%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (34 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1864 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(36 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 32 final=Some (Gval (Fuint 6) (global_word_1864 v)).
Proof.
 eapply global_node_1864_step.
 - exact (prior 1861%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (34 <= level)%coq_nat; lia))).
 - exact (prior 1863%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (35 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1865 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(37 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 33 final=Some (Gval (Fuint 5) (global_word_1865 v)).
Proof.
 eapply global_node_1865_step.
 - exact (prior 1864%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (36 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1866 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(38 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 34 final=Some (Gval (Fuint 1) (global_word_1866 v)).
Proof.
 eapply global_node_1866_step.
 - exact (prior 1856%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (22 <= level)%coq_nat; lia))).
 - exact (prior 1865%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1867 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 1 final=Some (Gval (Fuint 1) (global_word_1867 v)).
Proof.
 apply (global_sync_1867_link invalid snapshot final v); [eapply global_progress_1331; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1868 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 35 final=Some (Gval (Fuint 1) (global_word_1868 v)).
Proof.
 eapply global_node_1868_step.
 - exact (prior 1867%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1869 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 36 final=Some (Gval (Fuint 1) (global_word_1869 v)).
Proof.
 eapply global_node_1869_step.
 - exact (prior 1868%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1870 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(39 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 37 final=Some (Gval (Fuint 1) (global_word_1870 v)).
Proof.
 eapply global_node_1870_step.
 - exact (prior 1866%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (38 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1871 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 0 final=Some (Gval Fclock (global_word_1871 v)).
Proof.
 apply (global_sync_1871_link invalid snapshot final v); [eapply global_progress_1330; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1872 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::17] 10 0 final=Some (Gval Fclock (global_word_1872 v)).
Proof.
 have Typed := types 1872%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1872_step.
 - exact (prior 1871%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - reflexivity.
 - exact ran.
Qed.
Lemma global_progress_1873 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::17] 10 1 final=Some (Gval (Fuint 1) (global_word_1873 v)).
Proof.
 have Typed := types 1873%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1873_step.
 - exact (prior 1867%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1873 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1874 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::17] 11 0 final=Some (Gval Fclock (global_word_1874 v)).
Proof.
 have Typed := types 1874%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1874_step.
 - exact (prior 1871%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - reflexivity.
 - exact ran.
Qed.
Lemma global_progress_1875 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::17] 11 1 final=Some (Gval (Fuint 1) (global_word_1875 v)).
Proof.
 have Typed := types 1875%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1875_step.
 - exact (prior 1867%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1875 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1876 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 7 final=Some (Gval (Fuint 4) (global_word_1876 v)).
Proof.
 eapply global_node_1876_step.
 - exact (prior 790%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1877 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 8 final=Some (Gval (Fuint 4) (global_word_1877 v)).
Proof.
 eapply global_node_1877_step.
 - exact (prior 795%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1878 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 9 final=Some (Gval (Fuint 4) (global_word_1878 v)).
Proof.
 eapply global_node_1878_step.
 - exact (prior 785%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1879 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 10 final=Some (Gval (Fuint 5) (global_word_1879 v)).
Proof.
 eapply global_node_1879_step.
 - exact (prior 1876%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 1877%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1880 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(7 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 11 final=Some (Gval (Fuint 4) (global_word_1880 v)).
Proof.
 eapply global_node_1880_step.
 - exact (prior 1879%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1881 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(8 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 12 final=Some (Gval (Fuint 5) (global_word_1881 v)).
Proof.
 eapply global_node_1881_step.
 - exact (prior 1880%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (7 <= level)%coq_nat; lia))).
 - exact (prior 1878%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1882 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(9 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 13 final=Some (Gval (Fuint 4) (global_word_1882 v)).
Proof.
 eapply global_node_1882_step.
 - exact (prior 1881%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (8 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1883 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 14 final=Some (Gval (Fuint 4) (global_word_1883 v)).
Proof.
 eapply global_node_1883_step.
 - exact (prior 805%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (12 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1884 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 15 final=Some (Gval (Fuint 4) (global_word_1884 v)).
Proof.
 eapply global_node_1884_step.
 - exact (prior 832%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (12 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1885 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 16 final=Some (Gval (Fuint 5) (global_word_1885 v)).
Proof.
 eapply global_node_1885_step.
 - exact (prior 1884%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1886 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 17 final=Some (Gval (Fuint 6) (global_word_1886 v)).
Proof.
 eapply global_node_1886_step.
 - exact (prior 1883%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact (prior 1885%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1887 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 18 final=Some (Gval (Fuint 5) (global_word_1887 v)).
Proof.
 eapply global_node_1887_step.
 - exact (prior 1886%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1888 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(17 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 19 final=Some (Gval (Fuint 1) (global_word_1888 v)).
Proof.
 eapply global_node_1888_step.
 - exact (prior 1882%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (9 <= level)%coq_nat; lia))).
 - exact (prior 1887%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1889 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 1 final=Some (Gval (Fuint 1) (global_word_1889 v)).
Proof.
 apply (global_sync_1889_link invalid snapshot final v); [eapply global_progress_1873; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1890 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 20 final=Some (Gval (Fuint 1) (global_word_1890 v)).
Proof.
 eapply global_node_1890_step.
 - exact (prior 1889%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1891 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 21 final=Some (Gval (Fuint 1) (global_word_1891 v)).
Proof.
 eapply global_node_1891_step.
 - exact (prior 1890%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1892 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 22 final=Some (Gval (Fuint 1) (global_word_1892 v)).
Proof.
 eapply global_node_1892_step.
 - exact (prior 1888%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1893 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 0 final=Some (Gval Fclock (global_word_1893 v)).
Proof.
 apply (global_sync_1893_link invalid snapshot final v); [eapply global_progress_1872; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1894 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(17 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 7 final=Some (Gval (Fuint 4) (global_word_1894 v)).
Proof.
 eapply global_node_1894_step.
 - exact (prior 809%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1895 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 8 final=Some (Gval (Fuint 4) (global_word_1895 v)).
Proof.
 eapply global_node_1895_step.
 - exact (prior 815%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1896 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(23 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 9 final=Some (Gval (Fuint 4) (global_word_1896 v)).
Proof.
 eapply global_node_1896_step.
 - exact (prior 780%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (22 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1897 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 10 final=Some (Gval (Fuint 5) (global_word_1897 v)).
Proof.
 eapply global_node_1897_step.
 - exact (prior 1894%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact (prior 1895%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1898 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(19 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 11 final=Some (Gval (Fuint 4) (global_word_1898 v)).
Proof.
 eapply global_node_1898_step.
 - exact (prior 1897%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1899 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(24 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 12 final=Some (Gval (Fuint 5) (global_word_1899 v)).
Proof.
 eapply global_node_1899_step.
 - exact (prior 1898%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (19 <= level)%coq_nat; lia))).
 - exact (prior 1896%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (23 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1900 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(25 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 13 final=Some (Gval (Fuint 4) (global_word_1900 v)).
Proof.
 eapply global_node_1900_step.
 - exact (prior 1899%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (24 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1901 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(30 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 14 final=Some (Gval (Fuint 4) (global_word_1901 v)).
Proof.
 eapply global_node_1901_step.
 - exact (prior 825%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (29 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1902 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(30 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 15 final=Some (Gval (Fuint 4) (global_word_1902 v)).
Proof.
 eapply global_node_1902_step.
 - exact (prior 839%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (29 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1903 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(31 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 16 final=Some (Gval (Fuint 5) (global_word_1903 v)).
Proof.
 eapply global_node_1903_step.
 - exact (prior 1902%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (30 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1904 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(32 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 17 final=Some (Gval (Fuint 6) (global_word_1904 v)).
Proof.
 eapply global_node_1904_step.
 - exact (prior 1901%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (30 <= level)%coq_nat; lia))).
 - exact (prior 1903%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (31 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1905 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(33 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 18 final=Some (Gval (Fuint 5) (global_word_1905 v)).
Proof.
 eapply global_node_1905_step.
 - exact (prior 1904%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (32 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1906 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(34 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 19 final=Some (Gval (Fuint 1) (global_word_1906 v)).
Proof.
 eapply global_node_1906_step.
 - exact (prior 1900%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (25 <= level)%coq_nat; lia))).
 - exact (prior 1905%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (33 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1907 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 1 final=Some (Gval (Fuint 1) (global_word_1907 v)).
Proof.
 apply (global_sync_1907_link invalid snapshot final v); [eapply global_progress_1875; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1908 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 20 final=Some (Gval (Fuint 1) (global_word_1908 v)).
Proof.
 eapply global_node_1908_step.
 - exact (prior 1907%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1909 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 21 final=Some (Gval (Fuint 1) (global_word_1909 v)).
Proof.
 eapply global_node_1909_step.
 - exact (prior 1908%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1910 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(35 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 22 final=Some (Gval (Fuint 1) (global_word_1910 v)).
Proof.
 eapply global_node_1910_step.
 - exact (prior 1906%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (34 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1911 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 0 final=Some (Gval Fclock (global_word_1911 v)).
Proof.
 apply (global_sync_1911_link invalid snapshot final v); [eapply global_progress_1874; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1912 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 12 final=Some (Gval (Fuint 4) (global_word_1912 v)).
Proof.
 eapply global_node_1912_step.
 - exact (prior 857%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1913 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 13 final=Some (Gval (Fuint 4) (global_word_1913 v)).
Proof.
 eapply global_node_1913_step.
 - exact (prior 862%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1914 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 14 final=Some (Gval (Fuint 4) (global_word_1914 v)).
Proof.
 eapply global_node_1914_step.
 - exact (prior 852%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1915 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 15 final=Some (Gval (Fuint 4) (global_word_1915 v)).
Proof.
 eapply global_node_1915_step.
 - exact (prior 881%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1916 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(20 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 16 final=Some (Gval (Fuint 4) (global_word_1916 v)).
Proof.
 eapply global_node_1916_step.
 - exact (prior 846%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (19 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1917 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 17 final=Some (Gval (Fuint 5) (global_word_1917 v)).
Proof.
 eapply global_node_1917_step.
 - exact (prior 1912%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact (prior 1913%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1918 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 18 final=Some (Gval (Fuint 4) (global_word_1918 v)).
Proof.
 eapply global_node_1918_step.
 - exact (prior 1917%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1919 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 19 final=Some (Gval (Fuint 5) (global_word_1919 v)).
Proof.
 eapply global_node_1919_step.
 - exact (prior 1914%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact (prior 1918%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1920 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(7 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 20 final=Some (Gval (Fuint 4) (global_word_1920 v)).
Proof.
 eapply global_node_1920_step.
 - exact (prior 1919%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1921 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(8 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 21 final=Some (Gval (Fuint 5) (global_word_1921 v)).
Proof.
 eapply global_node_1921_step.
 - exact (prior 1915%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact (prior 1920%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (7 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1922 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(9 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 22 final=Some (Gval (Fuint 4) (global_word_1922 v)).
Proof.
 eapply global_node_1922_step.
 - exact (prior 1921%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (8 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1923 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(21 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 23 final=Some (Gval (Fuint 5) (global_word_1923 v)).
Proof.
 eapply global_node_1923_step.
 - exact (prior 1916%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (20 <= level)%coq_nat; lia))).
 - exact (prior 1922%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (9 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1924 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(22 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 24 final=Some (Gval (Fuint 4) (global_word_1924 v)).
Proof.
 eapply global_node_1924_step.
 - exact (prior 1923%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (21 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1925 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(33 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 25 final=Some (Gval (Fuint 4) (global_word_1925 v)).
Proof.
 eapply global_node_1925_step.
 - exact (prior 897%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (32 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1926 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 26 final=Some (Gval (Fuint 4) (global_word_1926 v)).
Proof.
 eapply global_node_1926_step.
 - exact (prior 904%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1927 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(17 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 27 final=Some (Gval (Fuint 5) (global_word_1927 v)).
Proof.
 eapply global_node_1927_step.
 - exact (prior 1926%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1928 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(33 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 28 final=Some (Gval (Fuint 4) (global_word_1928 v)).
Proof.
 eapply global_node_1928_step.
 - exact (prior 911%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (32 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1929 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(34 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 29 final=Some (Gval (Fuint 5) (global_word_1929 v)).
Proof.
 eapply global_node_1929_step.
 - exact (prior 1928%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (33 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1930 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(34 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 30 final=Some (Gval (Fuint 6) (global_word_1930 v)).
Proof.
 eapply global_node_1930_step.
 - exact (prior 1925%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (33 <= level)%coq_nat; lia))).
 - exact (prior 1927%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1931 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(35 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 31 final=Some (Gval (Fuint 5) (global_word_1931 v)).
Proof.
 eapply global_node_1931_step.
 - exact (prior 1930%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (34 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1932 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(36 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 32 final=Some (Gval (Fuint 6) (global_word_1932 v)).
Proof.
 eapply global_node_1932_step.
 - exact (prior 1929%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (34 <= level)%coq_nat; lia))).
 - exact (prior 1931%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (35 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1933 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(37 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 33 final=Some (Gval (Fuint 5) (global_word_1933 v)).
Proof.
 eapply global_node_1933_step.
 - exact (prior 1932%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (36 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1934 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(38 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 34 final=Some (Gval (Fuint 1) (global_word_1934 v)).
Proof.
 eapply global_node_1934_step.
 - exact (prior 1924%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (22 <= level)%coq_nat; lia))).
 - exact (prior 1933%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1935 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 1 final=Some (Gval (Fuint 1) (global_word_1935 v)).
Proof.
 apply (global_sync_1935_link invalid snapshot final v); [eapply global_progress_1333; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1936 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 35 final=Some (Gval (Fuint 1) (global_word_1936 v)).
Proof.
 eapply global_node_1936_step.
 - exact (prior 1935%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1937 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 36 final=Some (Gval (Fuint 1) (global_word_1937 v)).
Proof.
 eapply global_node_1937_step.
 - exact (prior 1936%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1938 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(39 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 37 final=Some (Gval (Fuint 1) (global_word_1938 v)).
Proof.
 eapply global_node_1938_step.
 - exact (prior 1934%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (38 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1939 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 0 final=Some (Gval Fclock (global_word_1939 v)).
Proof.
 apply (global_sync_1939_link invalid snapshot final v); [eapply global_progress_1332; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1940 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::18] 10 0 final=Some (Gval Fclock (global_word_1940 v)).
Proof.
 have Typed := types 1940%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1940_step.
 - exact (prior 1939%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - reflexivity.
 - exact ran.
Qed.
Lemma global_progress_1941 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::18] 10 1 final=Some (Gval (Fuint 1) (global_word_1941 v)).
Proof.
 have Typed := types 1941%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1941_step.
 - exact (prior 1935%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1941 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1942 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::18] 11 0 final=Some (Gval Fclock (global_word_1942 v)).
Proof.
 have Typed := types 1942%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1942_step.
 - exact (prior 1939%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - reflexivity.
 - exact ran.
Qed.
Lemma global_progress_1943 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::18] 11 1 final=Some (Gval (Fuint 1) (global_word_1943 v)).
Proof.
 have Typed := types 1943%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1943_step.
 - exact (prior 1935%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1943 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1944 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 7 final=Some (Gval (Fuint 4) (global_word_1944 v)).
Proof.
 eapply global_node_1944_step.
 - exact (prior 859%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1945 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 8 final=Some (Gval (Fuint 4) (global_word_1945 v)).
Proof.
 eapply global_node_1945_step.
 - exact (prior 864%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1946 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 9 final=Some (Gval (Fuint 4) (global_word_1946 v)).
Proof.
 eapply global_node_1946_step.
 - exact (prior 854%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1947 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 10 final=Some (Gval (Fuint 5) (global_word_1947 v)).
Proof.
 eapply global_node_1947_step.
 - exact (prior 1944%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 1945%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1948 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(7 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 11 final=Some (Gval (Fuint 4) (global_word_1948 v)).
Proof.
 eapply global_node_1948_step.
 - exact (prior 1947%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1949 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(8 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 12 final=Some (Gval (Fuint 5) (global_word_1949 v)).
Proof.
 eapply global_node_1949_step.
 - exact (prior 1948%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (7 <= level)%coq_nat; lia))).
 - exact (prior 1946%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1950 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(9 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 13 final=Some (Gval (Fuint 4) (global_word_1950 v)).
Proof.
 eapply global_node_1950_step.
 - exact (prior 1949%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (8 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1951 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 14 final=Some (Gval (Fuint 4) (global_word_1951 v)).
Proof.
 eapply global_node_1951_step.
 - exact (prior 874%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (12 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1952 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 15 final=Some (Gval (Fuint 4) (global_word_1952 v)).
Proof.
 eapply global_node_1952_step.
 - exact (prior 901%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (12 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1953 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 16 final=Some (Gval (Fuint 5) (global_word_1953 v)).
Proof.
 eapply global_node_1953_step.
 - exact (prior 1952%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1954 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 17 final=Some (Gval (Fuint 6) (global_word_1954 v)).
Proof.
 eapply global_node_1954_step.
 - exact (prior 1951%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact (prior 1953%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1955 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 18 final=Some (Gval (Fuint 5) (global_word_1955 v)).
Proof.
 eapply global_node_1955_step.
 - exact (prior 1954%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1956 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(17 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 19 final=Some (Gval (Fuint 1) (global_word_1956 v)).
Proof.
 eapply global_node_1956_step.
 - exact (prior 1950%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (9 <= level)%coq_nat; lia))).
 - exact (prior 1955%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1957 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 1 final=Some (Gval (Fuint 1) (global_word_1957 v)).
Proof.
 apply (global_sync_1957_link invalid snapshot final v); [eapply global_progress_1941; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1958 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 20 final=Some (Gval (Fuint 1) (global_word_1958 v)).
Proof.
 eapply global_node_1958_step.
 - exact (prior 1957%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1959 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 21 final=Some (Gval (Fuint 1) (global_word_1959 v)).
Proof.
 eapply global_node_1959_step.
 - exact (prior 1958%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1960 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 22 final=Some (Gval (Fuint 1) (global_word_1960 v)).
Proof.
 eapply global_node_1960_step.
 - exact (prior 1956%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1961 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 0 final=Some (Gval Fclock (global_word_1961 v)).
Proof.
 apply (global_sync_1961_link invalid snapshot final v); [eapply global_progress_1940; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1962 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(17 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 7 final=Some (Gval (Fuint 4) (global_word_1962 v)).
Proof.
 eapply global_node_1962_step.
 - exact (prior 878%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1963 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 8 final=Some (Gval (Fuint 4) (global_word_1963 v)).
Proof.
 eapply global_node_1963_step.
 - exact (prior 884%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1964 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(23 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 9 final=Some (Gval (Fuint 4) (global_word_1964 v)).
Proof.
 eapply global_node_1964_step.
 - exact (prior 849%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (22 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1965 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 10 final=Some (Gval (Fuint 5) (global_word_1965 v)).
Proof.
 eapply global_node_1965_step.
 - exact (prior 1962%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact (prior 1963%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1966 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(19 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 11 final=Some (Gval (Fuint 4) (global_word_1966 v)).
Proof.
 eapply global_node_1966_step.
 - exact (prior 1965%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1967 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(24 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 12 final=Some (Gval (Fuint 5) (global_word_1967 v)).
Proof.
 eapply global_node_1967_step.
 - exact (prior 1966%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (19 <= level)%coq_nat; lia))).
 - exact (prior 1964%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (23 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1968 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(25 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 13 final=Some (Gval (Fuint 4) (global_word_1968 v)).
Proof.
 eapply global_node_1968_step.
 - exact (prior 1967%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (24 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1969 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(30 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 14 final=Some (Gval (Fuint 4) (global_word_1969 v)).
Proof.
 eapply global_node_1969_step.
 - exact (prior 894%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (29 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1970 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(30 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 15 final=Some (Gval (Fuint 4) (global_word_1970 v)).
Proof.
 eapply global_node_1970_step.
 - exact (prior 908%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (29 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1971 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(31 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 16 final=Some (Gval (Fuint 5) (global_word_1971 v)).
Proof.
 eapply global_node_1971_step.
 - exact (prior 1970%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (30 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1972 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(32 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 17 final=Some (Gval (Fuint 6) (global_word_1972 v)).
Proof.
 eapply global_node_1972_step.
 - exact (prior 1969%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (30 <= level)%coq_nat; lia))).
 - exact (prior 1971%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (31 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1973 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(33 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 18 final=Some (Gval (Fuint 5) (global_word_1973 v)).
Proof.
 eapply global_node_1973_step.
 - exact (prior 1972%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (32 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1974 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(34 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 19 final=Some (Gval (Fuint 1) (global_word_1974 v)).
Proof.
 eapply global_node_1974_step.
 - exact (prior 1968%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (25 <= level)%coq_nat; lia))).
 - exact (prior 1973%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (33 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1975 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 1 final=Some (Gval (Fuint 1) (global_word_1975 v)).
Proof.
 apply (global_sync_1975_link invalid snapshot final v); [eapply global_progress_1943; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1976 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 20 final=Some (Gval (Fuint 1) (global_word_1976 v)).
Proof.
 eapply global_node_1976_step.
 - exact (prior 1975%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1977 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 21 final=Some (Gval (Fuint 1) (global_word_1977 v)).
Proof.
 eapply global_node_1977_step.
 - exact (prior 1976%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1978 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(35 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 22 final=Some (Gval (Fuint 1) (global_word_1978 v)).
Proof.
 eapply global_node_1978_step.
 - exact (prior 1974%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (34 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1979 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 0 final=Some (Gval Fclock (global_word_1979 v)).
Proof.
 apply (global_sync_1979_link invalid snapshot final v); [eapply global_progress_1942; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1980 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 7 final=Some (Gval (Fuint 4) (global_word_1980 v)).
Proof.
 eapply global_node_1980_step.
 - exact (prior 918%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1981 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 8 final=Some (Gval (Fuint 4) (global_word_1981 v)).
Proof.
 eapply global_node_1981_step.
 - exact (prior 921%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1982 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 9 final=Some (Gval (Fuint 4) (global_word_1982 v)).
Proof.
 eapply global_node_1982_step.
 - exact (prior 915%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1983 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 10 final=Some (Gval (Fuint 5) (global_word_1983 v)).
Proof.
 eapply global_node_1983_step.
 - exact (prior 1980%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact (prior 1981%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1984 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 11 final=Some (Gval (Fuint 4) (global_word_1984 v)).
Proof.
 eapply global_node_1984_step.
 - exact (prior 1983%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1985 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 12 final=Some (Gval (Fuint 5) (global_word_1985 v)).
Proof.
 eapply global_node_1985_step.
 - exact (prior 1984%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 1982%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1986 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(7 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 13 final=Some (Gval (Fuint 4) (global_word_1986 v)).
Proof.
 eapply global_node_1986_step.
 - exact (prior 1985%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1987 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(11 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 14 final=Some (Gval (Fuint 4) (global_word_1987 v)).
Proof.
 eapply global_node_1987_step.
 - exact (prior 931%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (10 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1988 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(11 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 15 final=Some (Gval (Fuint 4) (global_word_1988 v)).
Proof.
 eapply global_node_1988_step.
 - exact (prior 935%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (10 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1989 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(12 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 16 final=Some (Gval (Fuint 5) (global_word_1989 v)).
Proof.
 eapply global_node_1989_step.
 - exact (prior 1988%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (11 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1990 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 17 final=Some (Gval (Fuint 6) (global_word_1990 v)).
Proof.
 eapply global_node_1990_step.
 - exact (prior 1987%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (11 <= level)%coq_nat; lia))).
 - exact (prior 1989%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (12 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1991 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 18 final=Some (Gval (Fuint 5) (global_word_1991 v)).
Proof.
 eapply global_node_1991_step.
 - exact (prior 1990%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1992 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 19 final=Some (Gval (Fuint 1) (global_word_1992 v)).
Proof.
 eapply global_node_1992_step.
 - exact (prior 1986%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (7 <= level)%coq_nat; lia))).
 - exact (prior 1991%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1993 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 1 final=Some (Gval (Fuint 1) (global_word_1993 v)).
Proof.
 apply (global_sync_1993_link invalid snapshot final v); [eapply global_progress_1335; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1994 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 20 final=Some (Gval (Fuint 1) (global_word_1994 v)).
Proof.
 eapply global_node_1994_step.
 - exact (prior 1993%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1995 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 21 final=Some (Gval (Fuint 1) (global_word_1995 v)).
Proof.
 eapply global_node_1995_step.
 - exact (prior 1994%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1996 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 22 final=Some (Gval (Fuint 1) (global_word_1996 v)).
Proof.
 eapply global_node_1996_step.
 - exact (prior 1992%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1997 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 0 final=Some (Gval Fclock (global_word_1997 v)).
Proof.
 apply (global_sync_1997_link invalid snapshot final v); [eapply global_progress_1334; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1998 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::20] 6 final=Some (Gval (Fuint 4) (global_word_1998 v)).
Proof.
 eapply global_node_1998_step.
 - exact (prior 939%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1999 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::20] 7 final=Some (Gval (Fuint 4) (global_word_1999 v)).
Proof.
 eapply global_node_1999_step.
 - exact (prior 942%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
