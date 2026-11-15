From Coq Require Import NArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import HierarchyFacts PortFieldFacts.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalWidthFacts GlobalNodeSteps GlobalFieldSteps GlobalScalarSteps GlobalSyncSteps GlobalLeaves.
Local Open Scope N_scope.
From SmallMultiplier Require Import GlobalProgressTypes.
From SmallMultiplier Require Export GlobalProgress9.
Lemma global_progress_2000 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::20] 8 final=Some (Gval (Fuint 5) (global_word_2000 v)).
Proof.
 eapply global_node_2000_step.
 - exact (prior 1998%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact (prior 1999%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2001 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::20] 9 final=Some (Gval (Fuint 4) (global_word_2001 v)).
Proof.
 eapply global_node_2001_step.
 - exact (prior 2000%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2002 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(9 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::20] 10 final=Some (Gval (Fuint 4) (global_word_2002 v)).
Proof.
 eapply global_node_2002_step.
 - exact (prior 949%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (8 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2003 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(9 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::20] 11 final=Some (Gval (Fuint 4) (global_word_2003 v)).
Proof.
 eapply global_node_2003_step.
 - exact (prior 953%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (8 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2004 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(10 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::20] 12 final=Some (Gval (Fuint 5) (global_word_2004 v)).
Proof.
 eapply global_node_2004_step.
 - exact (prior 2003%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (9 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2005 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(11 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::20] 13 final=Some (Gval (Fuint 6) (global_word_2005 v)).
Proof.
 eapply global_node_2005_step.
 - exact (prior 2002%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (9 <= level)%coq_nat; lia))).
 - exact (prior 2004%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (10 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2006 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(12 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::20] 14 final=Some (Gval (Fuint 5) (global_word_2006 v)).
Proof.
 eapply global_node_2006_step.
 - exact (prior 2005%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (11 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2007 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::20] 15 final=Some (Gval (Fuint 1) (global_word_2007 v)).
Proof.
 eapply global_node_2007_step.
 - exact (prior 2006%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (12 <= level)%coq_nat; lia))).
 - exact (prior 2001%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2008 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::20] 1 final=Some (Gval (Fuint 1) (global_word_2008 v)).
Proof.
 apply (global_sync_2008_link invalid snapshot final v); [eapply global_progress_1337; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_2009 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::20] 16 final=Some (Gval (Fuint 1) (global_word_2009 v)).
Proof.
 eapply global_node_2009_step.
 - exact (prior 2008%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2010 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::20] 17 final=Some (Gval (Fuint 1) (global_word_2010 v)).
Proof.
 eapply global_node_2010_step.
 - exact (prior 2009%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2011 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::20] 18 final=Some (Gval (Fuint 1) (global_word_2011 v)).
Proof.
 eapply global_node_2011_step.
 - exact (prior 2007%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2012 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::20] 0 final=Some (Gval Fclock (global_word_2012 v)).
Proof.
 apply (global_sync_2012_link invalid snapshot final v); [eapply global_progress_1336; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_2013 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::21] 6 final=Some (Gval (Fuint 4) (global_word_2013 v)).
Proof.
 eapply global_node_2013_step.
 - exact (prior 957%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2014 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::21] 7 final=Some (Gval (Fuint 4) (global_word_2014 v)).
Proof.
 eapply global_node_2014_step.
 - exact (prior 960%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2015 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::21] 8 final=Some (Gval (Fuint 5) (global_word_2015 v)).
Proof.
 eapply global_node_2015_step.
 - exact (prior 2013%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact (prior 2014%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2016 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::21] 9 final=Some (Gval (Fuint 4) (global_word_2016 v)).
Proof.
 eapply global_node_2016_step.
 - exact (prior 2015%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2017 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(9 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::21] 10 final=Some (Gval (Fuint 4) (global_word_2017 v)).
Proof.
 eapply global_node_2017_step.
 - exact (prior 967%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (8 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2018 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(9 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::21] 11 final=Some (Gval (Fuint 4) (global_word_2018 v)).
Proof.
 eapply global_node_2018_step.
 - exact (prior 971%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (8 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2019 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(10 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::21] 12 final=Some (Gval (Fuint 5) (global_word_2019 v)).
Proof.
 eapply global_node_2019_step.
 - exact (prior 2018%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (9 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2020 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(11 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::21] 13 final=Some (Gval (Fuint 6) (global_word_2020 v)).
Proof.
 eapply global_node_2020_step.
 - exact (prior 2017%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (9 <= level)%coq_nat; lia))).
 - exact (prior 2019%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (10 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2021 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(12 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::21] 14 final=Some (Gval (Fuint 5) (global_word_2021 v)).
Proof.
 eapply global_node_2021_step.
 - exact (prior 2020%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (11 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2022 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::21] 15 final=Some (Gval (Fuint 1) (global_word_2022 v)).
Proof.
 eapply global_node_2022_step.
 - exact (prior 2021%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (12 <= level)%coq_nat; lia))).
 - exact (prior 2016%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2023 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::21] 1 final=Some (Gval (Fuint 1) (global_word_2023 v)).
Proof.
 apply (global_sync_2023_link invalid snapshot final v); [eapply global_progress_1339; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_2024 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::21] 16 final=Some (Gval (Fuint 1) (global_word_2024 v)).
Proof.
 eapply global_node_2024_step.
 - exact (prior 2023%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2025 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::21] 17 final=Some (Gval (Fuint 1) (global_word_2025 v)).
Proof.
 eapply global_node_2025_step.
 - exact (prior 2024%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2026 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::21] 18 final=Some (Gval (Fuint 1) (global_word_2026 v)).
Proof.
 eapply global_node_2026_step.
 - exact (prior 2022%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2027 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::21] 0 final=Some (Gval Fclock (global_word_2027 v)).
Proof.
 apply (global_sync_2027_link invalid snapshot final v); [eapply global_progress_1338; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_2028 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::22] 6 final=Some (Gval (Fuint 4) (global_word_2028 v)).
Proof.
 eapply global_node_2028_step.
 - exact (prior 975%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (12 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2029 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::22] 7 final=Some (Gval (Fuint 4) (global_word_2029 v)).
Proof.
 eapply global_node_2029_step.
 - exact (prior 978%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (12 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2030 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::22] 8 final=Some (Gval (Fuint 5) (global_word_2030 v)).
Proof.
 eapply global_node_2030_step.
 - exact (prior 2028%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact (prior 2029%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2031 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::22] 9 final=Some (Gval (Fuint 4) (global_word_2031 v)).
Proof.
 eapply global_node_2031_step.
 - exact (prior 2030%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2032 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(19 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::22] 10 final=Some (Gval (Fuint 4) (global_word_2032 v)).
Proof.
 eapply global_node_2032_step.
 - exact (prior 985%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2033 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(19 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::22] 11 final=Some (Gval (Fuint 4) (global_word_2033 v)).
Proof.
 eapply global_node_2033_step.
 - exact (prior 989%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2034 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(20 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::22] 12 final=Some (Gval (Fuint 5) (global_word_2034 v)).
Proof.
 eapply global_node_2034_step.
 - exact (prior 2033%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (19 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2035 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(21 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::22] 13 final=Some (Gval (Fuint 6) (global_word_2035 v)).
Proof.
 eapply global_node_2035_step.
 - exact (prior 2032%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (19 <= level)%coq_nat; lia))).
 - exact (prior 2034%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (20 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2036 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(22 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::22] 14 final=Some (Gval (Fuint 5) (global_word_2036 v)).
Proof.
 eapply global_node_2036_step.
 - exact (prior 2035%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (21 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2037 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(23 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::22] 15 final=Some (Gval (Fuint 1) (global_word_2037 v)).
Proof.
 eapply global_node_2037_step.
 - exact (prior 2036%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (22 <= level)%coq_nat; lia))).
 - exact (prior 2031%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2038 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::22] 1 final=Some (Gval (Fuint 1) (global_word_2038 v)).
Proof.
 apply (global_sync_2038_link invalid snapshot final v); [eapply global_progress_1341; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_2039 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::22] 16 final=Some (Gval (Fuint 1) (global_word_2039 v)).
Proof.
 eapply global_node_2039_step.
 - exact (prior 2038%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2040 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::22] 17 final=Some (Gval (Fuint 1) (global_word_2040 v)).
Proof.
 eapply global_node_2040_step.
 - exact (prior 2039%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2041 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(24 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::22] 18 final=Some (Gval (Fuint 1) (global_word_2041 v)).
Proof.
 eapply global_node_2041_step.
 - exact (prior 2037%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (23 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2042 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::22] 0 final=Some (Gval Fclock (global_word_2042 v)).
Proof.
 apply (global_sync_2042_link invalid snapshot final v); [eapply global_progress_1340; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_2043 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::23] 6 final=Some (Gval (Fuint 4) (global_word_2043 v)).
Proof.
 eapply global_node_2043_step.
 - exact (prior 993%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2044 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::23] 7 final=Some (Gval (Fuint 4) (global_word_2044 v)).
Proof.
 eapply global_node_2044_step.
 - exact (prior 996%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (12 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2045 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::23] 8 final=Some (Gval (Fuint 5) (global_word_2045 v)).
Proof.
 eapply global_node_2045_step.
 - exact (prior 2043%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 2044%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2046 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(17 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::23] 9 final=Some (Gval (Fuint 4) (global_word_2046 v)).
Proof.
 eapply global_node_2046_step.
 - exact (prior 2045%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2047 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(21 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::23] 10 final=Some (Gval (Fuint 4) (global_word_2047 v)).
Proof.
 eapply global_node_2047_step.
 - exact (prior 1003%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (20 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2048 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(21 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::23] 11 final=Some (Gval (Fuint 4) (global_word_2048 v)).
Proof.
 eapply global_node_2048_step.
 - exact (prior 1007%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (20 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2049 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(22 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::23] 12 final=Some (Gval (Fuint 5) (global_word_2049 v)).
Proof.
 eapply global_node_2049_step.
 - exact (prior 2048%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (21 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2050 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(23 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::23] 13 final=Some (Gval (Fuint 6) (global_word_2050 v)).
Proof.
 eapply global_node_2050_step.
 - exact (prior 2047%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (21 <= level)%coq_nat; lia))).
 - exact (prior 2049%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (22 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2051 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(24 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::23] 14 final=Some (Gval (Fuint 5) (global_word_2051 v)).
Proof.
 eapply global_node_2051_step.
 - exact (prior 2050%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (23 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2052 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(25 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::23] 15 final=Some (Gval (Fuint 1) (global_word_2052 v)).
Proof.
 eapply global_node_2052_step.
 - exact (prior 2051%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (24 <= level)%coq_nat; lia))).
 - exact (prior 2046%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2053 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::23] 1 final=Some (Gval (Fuint 1) (global_word_2053 v)).
Proof.
 apply (global_sync_2053_link invalid snapshot final v); [eapply global_progress_1343; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_2054 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::23] 16 final=Some (Gval (Fuint 1) (global_word_2054 v)).
Proof.
 eapply global_node_2054_step.
 - exact (prior 2053%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2055 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::23] 17 final=Some (Gval (Fuint 1) (global_word_2055 v)).
Proof.
 eapply global_node_2055_step.
 - exact (prior 2054%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2056 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(26 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::23] 18 final=Some (Gval (Fuint 1) (global_word_2056 v)).
Proof.
 eapply global_node_2056_step.
 - exact (prior 2052%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (25 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2057 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::23] 0 final=Some (Gval Fclock (global_word_2057 v)).
Proof.
 apply (global_sync_2057_link invalid snapshot final v); [eapply global_progress_1342; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_2058 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::24] 6 final=Some (Gval (Fuint 4) (global_word_2058 v)).
Proof.
 eapply global_node_2058_step.
 - exact (prior 1011%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2059 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::24] 7 final=Some (Gval (Fuint 4) (global_word_2059 v)).
Proof.
 eapply global_node_2059_step.
 - exact (prior 1014%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2060 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::24] 8 final=Some (Gval (Fuint 5) (global_word_2060 v)).
Proof.
 eapply global_node_2060_step.
 - exact (prior 2058%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 2059%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2061 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(17 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::24] 9 final=Some (Gval (Fuint 4) (global_word_2061 v)).
Proof.
 eapply global_node_2061_step.
 - exact (prior 2060%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2062 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(21 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::24] 10 final=Some (Gval (Fuint 4) (global_word_2062 v)).
Proof.
 eapply global_node_2062_step.
 - exact (prior 1021%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (20 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2063 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(21 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::24] 11 final=Some (Gval (Fuint 4) (global_word_2063 v)).
Proof.
 eapply global_node_2063_step.
 - exact (prior 1025%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (20 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2064 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(22 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::24] 12 final=Some (Gval (Fuint 5) (global_word_2064 v)).
Proof.
 eapply global_node_2064_step.
 - exact (prior 2063%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (21 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2065 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(23 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::24] 13 final=Some (Gval (Fuint 6) (global_word_2065 v)).
Proof.
 eapply global_node_2065_step.
 - exact (prior 2062%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (21 <= level)%coq_nat; lia))).
 - exact (prior 2064%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (22 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2066 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(24 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::24] 14 final=Some (Gval (Fuint 5) (global_word_2066 v)).
Proof.
 eapply global_node_2066_step.
 - exact (prior 2065%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (23 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2067 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(25 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::24] 15 final=Some (Gval (Fuint 1) (global_word_2067 v)).
Proof.
 eapply global_node_2067_step.
 - exact (prior 2066%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (24 <= level)%coq_nat; lia))).
 - exact (prior 2061%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2068 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::24] 1 final=Some (Gval (Fuint 1) (global_word_2068 v)).
Proof.
 apply (global_sync_2068_link invalid snapshot final v); [eapply global_progress_1345; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_2069 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::24] 16 final=Some (Gval (Fuint 1) (global_word_2069 v)).
Proof.
 eapply global_node_2069_step.
 - exact (prior 2068%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2070 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::24] 17 final=Some (Gval (Fuint 1) (global_word_2070 v)).
Proof.
 eapply global_node_2070_step.
 - exact (prior 2069%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2071 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(26 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::24] 18 final=Some (Gval (Fuint 1) (global_word_2071 v)).
Proof.
 eapply global_node_2071_step.
 - exact (prior 2067%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (25 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2072 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::24] 0 final=Some (Gval Fclock (global_word_2072 v)).
Proof.
 apply (global_sync_2072_link invalid snapshot final v); [eapply global_progress_1344; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_2073 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(32 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::25] 6 final=Some (Gval (Fuint 4) (global_word_2073 v)).
Proof.
 eapply global_node_2073_step.
 - exact (prior 1029%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (31 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2074 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::25] 7 final=Some (Gval (Fuint 4) (global_word_2074 v)).
Proof.
 eapply global_node_2074_step.
 - exact (prior 1032%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2075 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(33 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::25] 8 final=Some (Gval (Fuint 5) (global_word_2075 v)).
Proof.
 eapply global_node_2075_step.
 - exact (prior 2073%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (32 <= level)%coq_nat; lia))).
 - exact (prior 2074%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2076 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(34 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::25] 9 final=Some (Gval (Fuint 4) (global_word_2076 v)).
Proof.
 eapply global_node_2076_step.
 - exact (prior 2075%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (33 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2077 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(38 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::25] 10 final=Some (Gval (Fuint 4) (global_word_2077 v)).
Proof.
 eapply global_node_2077_step.
 - exact (prior 1039%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2078 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(38 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::25] 11 final=Some (Gval (Fuint 4) (global_word_2078 v)).
Proof.
 eapply global_node_2078_step.
 - exact (prior 1043%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2079 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(39 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::25] 12 final=Some (Gval (Fuint 5) (global_word_2079 v)).
Proof.
 eapply global_node_2079_step.
 - exact (prior 2078%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (38 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2080 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(40 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::25] 13 final=Some (Gval (Fuint 6) (global_word_2080 v)).
Proof.
 eapply global_node_2080_step.
 - exact (prior 2077%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (38 <= level)%coq_nat; lia))).
 - exact (prior 2079%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (39 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2081 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(41 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::25] 14 final=Some (Gval (Fuint 5) (global_word_2081 v)).
Proof.
 eapply global_node_2081_step.
 - exact (prior 2080%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (40 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2082 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(42 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::25] 15 final=Some (Gval (Fuint 1) (global_word_2082 v)).
Proof.
 eapply global_node_2082_step.
 - exact (prior 2081%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (41 <= level)%coq_nat; lia))).
 - exact (prior 2076%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (34 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2083 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::25] 1 final=Some (Gval (Fuint 1) (global_word_2083 v)).
Proof.
 apply (global_sync_2083_link invalid snapshot final v); [eapply global_progress_1347; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_2084 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::25] 16 final=Some (Gval (Fuint 1) (global_word_2084 v)).
Proof.
 eapply global_node_2084_step.
 - exact (prior 2083%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2085 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::25] 17 final=Some (Gval (Fuint 1) (global_word_2085 v)).
Proof.
 eapply global_node_2085_step.
 - exact (prior 2084%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2086 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(43 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::25] 18 final=Some (Gval (Fuint 1) (global_word_2086 v)).
Proof.
 eapply global_node_2086_step.
 - exact (prior 2082%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (42 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2087 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::25] 0 final=Some (Gval Fclock (global_word_2087 v)).
Proof.
 apply (global_sync_2087_link invalid snapshot final v); [eapply global_progress_1346; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_2088 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(37 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::26] 6 final=Some (Gval (Fuint 4) (global_word_2088 v)).
Proof.
 eapply global_node_2088_step.
 - exact (prior 1047%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (36 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2089 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(32 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::26] 7 final=Some (Gval (Fuint 4) (global_word_2089 v)).
Proof.
 eapply global_node_2089_step.
 - exact (prior 1050%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (31 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2090 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(38 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::26] 8 final=Some (Gval (Fuint 5) (global_word_2090 v)).
Proof.
 eapply global_node_2090_step.
 - exact (prior 2088%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact (prior 2089%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (32 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2091 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(39 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::26] 9 final=Some (Gval (Fuint 4) (global_word_2091 v)).
Proof.
 eapply global_node_2091_step.
 - exact (prior 2090%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (38 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2092 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(43 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::26] 10 final=Some (Gval (Fuint 4) (global_word_2092 v)).
Proof.
 eapply global_node_2092_step.
 - exact (prior 1057%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (42 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2093 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(43 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::26] 11 final=Some (Gval (Fuint 4) (global_word_2093 v)).
Proof.
 eapply global_node_2093_step.
 - exact (prior 1061%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (42 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2094 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(44 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::26] 12 final=Some (Gval (Fuint 5) (global_word_2094 v)).
Proof.
 eapply global_node_2094_step.
 - exact (prior 2093%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (43 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2095 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(45 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::26] 13 final=Some (Gval (Fuint 6) (global_word_2095 v)).
Proof.
 eapply global_node_2095_step.
 - exact (prior 2092%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (43 <= level)%coq_nat; lia))).
 - exact (prior 2094%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (44 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2096 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(46 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::26] 14 final=Some (Gval (Fuint 5) (global_word_2096 v)).
Proof.
 eapply global_node_2096_step.
 - exact (prior 2095%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (45 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2097 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(47 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::26] 15 final=Some (Gval (Fuint 1) (global_word_2097 v)).
Proof.
 eapply global_node_2097_step.
 - exact (prior 2096%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (46 <= level)%coq_nat; lia))).
 - exact (prior 2091%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (39 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2098 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::26] 1 final=Some (Gval (Fuint 1) (global_word_2098 v)).
Proof.
 apply (global_sync_2098_link invalid snapshot final v); [eapply global_progress_1349; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_2099 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::26] 16 final=Some (Gval (Fuint 1) (global_word_2099 v)).
Proof.
 eapply global_node_2099_step.
 - exact (prior 2098%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2100 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::26] 17 final=Some (Gval (Fuint 1) (global_word_2100 v)).
Proof.
 eapply global_node_2100_step.
 - exact (prior 2099%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2101 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(48 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::26] 18 final=Some (Gval (Fuint 1) (global_word_2101 v)).
Proof.
 eapply global_node_2101_step.
 - exact (prior 2097%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (47 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2102 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::26] 0 final=Some (Gval Fclock (global_word_2102 v)).
Proof.
 apply (global_sync_2102_link invalid snapshot final v); [eapply global_progress_1348; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_2103 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(37 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 7 final=Some (Gval (Fuint 4) (global_word_2103 v)).
Proof.
 eapply global_node_2103_step.
 - exact (prior 1068%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (36 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2104 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 8 final=Some (Gval (Fuint 4) (global_word_2104 v)).
Proof.
 eapply global_node_2104_step.
 - exact (prior 1071%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2105 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(37 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 9 final=Some (Gval (Fuint 4) (global_word_2105 v)).
Proof.
 eapply global_node_2105_step.
 - exact (prior 1065%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (36 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2106 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(38 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 10 final=Some (Gval (Fuint 5) (global_word_2106 v)).
Proof.
 eapply global_node_2106_step.
 - exact (prior 2103%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact (prior 2104%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2107 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(39 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 11 final=Some (Gval (Fuint 4) (global_word_2107 v)).
Proof.
 eapply global_node_2107_step.
 - exact (prior 2106%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (38 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2108 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(40 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 12 final=Some (Gval (Fuint 5) (global_word_2108 v)).
Proof.
 eapply global_node_2108_step.
 - exact (prior 2107%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (39 <= level)%coq_nat; lia))).
 - exact (prior 2105%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2109 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(41 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 13 final=Some (Gval (Fuint 4) (global_word_2109 v)).
Proof.
 eapply global_node_2109_step.
 - exact (prior 2108%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (40 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2110 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(45 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 14 final=Some (Gval (Fuint 4) (global_word_2110 v)).
Proof.
 eapply global_node_2110_step.
 - exact (prior 1081%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (44 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2111 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(45 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 15 final=Some (Gval (Fuint 4) (global_word_2111 v)).
Proof.
 eapply global_node_2111_step.
 - exact (prior 1085%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (44 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2112 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(46 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 16 final=Some (Gval (Fuint 5) (global_word_2112 v)).
Proof.
 eapply global_node_2112_step.
 - exact (prior 2111%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (45 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2113 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(47 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 17 final=Some (Gval (Fuint 6) (global_word_2113 v)).
Proof.
 eapply global_node_2113_step.
 - exact (prior 2110%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (45 <= level)%coq_nat; lia))).
 - exact (prior 2112%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (46 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2114 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(48 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 18 final=Some (Gval (Fuint 5) (global_word_2114 v)).
Proof.
 eapply global_node_2114_step.
 - exact (prior 2113%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (47 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2115 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(49 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 19 final=Some (Gval (Fuint 1) (global_word_2115 v)).
Proof.
 eapply global_node_2115_step.
 - exact (prior 2109%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (41 <= level)%coq_nat; lia))).
 - exact (prior 2114%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (48 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2116 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 1 final=Some (Gval (Fuint 1) (global_word_2116 v)).
Proof.
 apply (global_sync_2116_link invalid snapshot final v); [eapply global_progress_1351; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_2117 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 20 final=Some (Gval (Fuint 1) (global_word_2117 v)).
Proof.
 eapply global_node_2117_step.
 - exact (prior 2116%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2118 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 21 final=Some (Gval (Fuint 1) (global_word_2118 v)).
Proof.
 eapply global_node_2118_step.
 - exact (prior 2117%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2119 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(50 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 22 final=Some (Gval (Fuint 1) (global_word_2119 v)).
Proof.
 eapply global_node_2119_step.
 - exact (prior 2115%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (49 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2120 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 0 final=Some (Gval Fclock (global_word_2120 v)).
Proof.
 apply (global_sync_2120_link invalid snapshot final v); [eapply global_progress_1350; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_2121 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(37 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 7 final=Some (Gval (Fuint 4) (global_word_2121 v)).
Proof.
 eapply global_node_2121_step.
 - exact (prior 1092%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (36 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2122 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 8 final=Some (Gval (Fuint 4) (global_word_2122 v)).
Proof.
 eapply global_node_2122_step.
 - exact (prior 1095%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2123 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(37 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 9 final=Some (Gval (Fuint 4) (global_word_2123 v)).
Proof.
 eapply global_node_2123_step.
 - exact (prior 1089%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (36 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2124 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(38 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 10 final=Some (Gval (Fuint 5) (global_word_2124 v)).
Proof.
 eapply global_node_2124_step.
 - exact (prior 2121%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact (prior 2122%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2125 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(39 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 11 final=Some (Gval (Fuint 4) (global_word_2125 v)).
Proof.
 eapply global_node_2125_step.
 - exact (prior 2124%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (38 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2126 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(40 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 12 final=Some (Gval (Fuint 5) (global_word_2126 v)).
Proof.
 eapply global_node_2126_step.
 - exact (prior 2125%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (39 <= level)%coq_nat; lia))).
 - exact (prior 2123%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2127 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(41 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 13 final=Some (Gval (Fuint 4) (global_word_2127 v)).
Proof.
 eapply global_node_2127_step.
 - exact (prior 2126%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (40 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2128 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(45 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 14 final=Some (Gval (Fuint 4) (global_word_2128 v)).
Proof.
 eapply global_node_2128_step.
 - exact (prior 1105%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (44 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2129 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(45 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 15 final=Some (Gval (Fuint 4) (global_word_2129 v)).
Proof.
 eapply global_node_2129_step.
 - exact (prior 1109%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (44 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2130 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(46 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 16 final=Some (Gval (Fuint 5) (global_word_2130 v)).
Proof.
 eapply global_node_2130_step.
 - exact (prior 2129%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (45 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2131 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(47 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 17 final=Some (Gval (Fuint 6) (global_word_2131 v)).
Proof.
 eapply global_node_2131_step.
 - exact (prior 2128%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (45 <= level)%coq_nat; lia))).
 - exact (prior 2130%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (46 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2132 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(48 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 18 final=Some (Gval (Fuint 5) (global_word_2132 v)).
Proof.
 eapply global_node_2132_step.
 - exact (prior 2131%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (47 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2133 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(49 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 19 final=Some (Gval (Fuint 1) (global_word_2133 v)).
Proof.
 eapply global_node_2133_step.
 - exact (prior 2127%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (41 <= level)%coq_nat; lia))).
 - exact (prior 2132%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (48 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2134 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 1 final=Some (Gval (Fuint 1) (global_word_2134 v)).
Proof.
 apply (global_sync_2134_link invalid snapshot final v); [eapply global_progress_1353; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_2135 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 20 final=Some (Gval (Fuint 1) (global_word_2135 v)).
Proof.
 eapply global_node_2135_step.
 - exact (prior 2134%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2136 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 21 final=Some (Gval (Fuint 1) (global_word_2136 v)).
Proof.
 eapply global_node_2136_step.
 - exact (prior 2135%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2137 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(50 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 22 final=Some (Gval (Fuint 1) (global_word_2137 v)).
Proof.
 eapply global_node_2137_step.
 - exact (prior 2133%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (49 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2138 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 0 final=Some (Gval Fclock (global_word_2138 v)).
Proof.
 apply (global_sync_2138_link invalid snapshot final v); [eapply global_progress_1352; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_2139 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(37 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::29] 6 final=Some (Gval (Fuint 4) (global_word_2139 v)).
Proof.
 eapply global_node_2139_step.
 - exact (prior 1113%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (36 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2140 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(37 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::29] 7 final=Some (Gval (Fuint 4) (global_word_2140 v)).
Proof.
 eapply global_node_2140_step.
 - exact (prior 1116%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (36 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2141 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(38 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::29] 8 final=Some (Gval (Fuint 5) (global_word_2141 v)).
Proof.
 eapply global_node_2141_step.
 - exact (prior 2139%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact (prior 2140%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2142 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(39 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::29] 9 final=Some (Gval (Fuint 4) (global_word_2142 v)).
Proof.
 eapply global_node_2142_step.
 - exact (prior 2141%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (38 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2143 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(43 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::29] 10 final=Some (Gval (Fuint 4) (global_word_2143 v)).
Proof.
 eapply global_node_2143_step.
 - exact (prior 1123%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (42 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2144 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(43 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::29] 11 final=Some (Gval (Fuint 4) (global_word_2144 v)).
Proof.
 eapply global_node_2144_step.
 - exact (prior 1127%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (42 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2145 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(44 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::29] 12 final=Some (Gval (Fuint 5) (global_word_2145 v)).
Proof.
 eapply global_node_2145_step.
 - exact (prior 2144%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (43 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2146 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(45 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::29] 13 final=Some (Gval (Fuint 6) (global_word_2146 v)).
Proof.
 eapply global_node_2146_step.
 - exact (prior 2143%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (43 <= level)%coq_nat; lia))).
 - exact (prior 2145%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (44 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2147 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(46 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::29] 14 final=Some (Gval (Fuint 5) (global_word_2147 v)).
Proof.
 eapply global_node_2147_step.
 - exact (prior 2146%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (45 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2148 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(47 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::29] 15 final=Some (Gval (Fuint 1) (global_word_2148 v)).
Proof.
 eapply global_node_2148_step.
 - exact (prior 2147%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (46 <= level)%coq_nat; lia))).
 - exact (prior 2142%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (39 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2149 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::29] 1 final=Some (Gval (Fuint 1) (global_word_2149 v)).
Proof.
 apply (global_sync_2149_link invalid snapshot final v); [eapply global_progress_1355; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_2150 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::29] 16 final=Some (Gval (Fuint 1) (global_word_2150 v)).
Proof.
 eapply global_node_2150_step.
 - exact (prior 2149%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2151 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::29] 17 final=Some (Gval (Fuint 1) (global_word_2151 v)).
Proof.
 eapply global_node_2151_step.
 - exact (prior 2150%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2152 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(48 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::29] 18 final=Some (Gval (Fuint 1) (global_word_2152 v)).
Proof.
 eapply global_node_2152_step.
 - exact (prior 2148%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (47 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2153 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::29] 0 final=Some (Gval Fclock (global_word_2153 v)).
Proof.
 apply (global_sync_2153_link invalid snapshot final v); [eapply global_progress_1354; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_2154 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(37 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::30] 6 final=Some (Gval (Fuint 4) (global_word_2154 v)).
Proof.
 eapply global_node_2154_step.
 - exact (prior 1131%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (36 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2155 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(37 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::30] 7 final=Some (Gval (Fuint 4) (global_word_2155 v)).
Proof.
 eapply global_node_2155_step.
 - exact (prior 1134%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (36 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2156 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(38 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::30] 8 final=Some (Gval (Fuint 5) (global_word_2156 v)).
Proof.
 eapply global_node_2156_step.
 - exact (prior 2154%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact (prior 2155%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2157 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(39 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::30] 9 final=Some (Gval (Fuint 4) (global_word_2157 v)).
Proof.
 eapply global_node_2157_step.
 - exact (prior 2156%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (38 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2158 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(43 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::30] 10 final=Some (Gval (Fuint 4) (global_word_2158 v)).
Proof.
 eapply global_node_2158_step.
 - exact (prior 1141%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (42 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2159 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(43 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::30] 11 final=Some (Gval (Fuint 4) (global_word_2159 v)).
Proof.
 eapply global_node_2159_step.
 - exact (prior 1145%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (42 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2160 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(44 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::30] 12 final=Some (Gval (Fuint 5) (global_word_2160 v)).
Proof.
 eapply global_node_2160_step.
 - exact (prior 2159%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (43 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2161 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(45 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::30] 13 final=Some (Gval (Fuint 6) (global_word_2161 v)).
Proof.
 eapply global_node_2161_step.
 - exact (prior 2158%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (43 <= level)%coq_nat; lia))).
 - exact (prior 2160%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (44 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2162 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(46 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::30] 14 final=Some (Gval (Fuint 5) (global_word_2162 v)).
Proof.
 eapply global_node_2162_step.
 - exact (prior 2161%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (45 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2163 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(47 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::30] 15 final=Some (Gval (Fuint 1) (global_word_2163 v)).
Proof.
 eapply global_node_2163_step.
 - exact (prior 2162%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (46 <= level)%coq_nat; lia))).
 - exact (prior 2157%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (39 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2164 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::30] 1 final=Some (Gval (Fuint 1) (global_word_2164 v)).
Proof.
 apply (global_sync_2164_link invalid snapshot final v); [eapply global_progress_1357; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_2165 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::30] 16 final=Some (Gval (Fuint 1) (global_word_2165 v)).
Proof.
 eapply global_node_2165_step.
 - exact (prior 2164%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2166 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::30] 17 final=Some (Gval (Fuint 1) (global_word_2166 v)).
Proof.
 eapply global_node_2166_step.
 - exact (prior 2165%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2167 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(48 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::30] 18 final=Some (Gval (Fuint 1) (global_word_2167 v)).
Proof.
 eapply global_node_2167_step.
 - exact (prior 2163%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (47 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2168 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::30] 0 final=Some (Gval Fclock (global_word_2168 v)).
Proof.
 apply (global_sync_2168_link invalid snapshot final v); [eapply global_progress_1356; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_2169 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(37 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::31] 6 final=Some (Gval (Fuint 4) (global_word_2169 v)).
Proof.
 eapply global_node_2169_step.
 - exact (prior 1149%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (36 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2170 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(37 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::31] 7 final=Some (Gval (Fuint 4) (global_word_2170 v)).
Proof.
 eapply global_node_2170_step.
 - exact (prior 1152%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (36 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2171 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(38 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::31] 8 final=Some (Gval (Fuint 5) (global_word_2171 v)).
Proof.
 eapply global_node_2171_step.
 - exact (prior 2169%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact (prior 2170%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2172 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(39 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::31] 9 final=Some (Gval (Fuint 4) (global_word_2172 v)).
Proof.
 eapply global_node_2172_step.
 - exact (prior 2171%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (38 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2173 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(43 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::31] 10 final=Some (Gval (Fuint 4) (global_word_2173 v)).
Proof.
 eapply global_node_2173_step.
 - exact (prior 1159%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (42 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2174 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(43 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::31] 11 final=Some (Gval (Fuint 4) (global_word_2174 v)).
Proof.
 eapply global_node_2174_step.
 - exact (prior 1163%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (42 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2175 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(44 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::31] 12 final=Some (Gval (Fuint 5) (global_word_2175 v)).
Proof.
 eapply global_node_2175_step.
 - exact (prior 2174%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (43 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2176 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(45 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::31] 13 final=Some (Gval (Fuint 6) (global_word_2176 v)).
Proof.
 eapply global_node_2176_step.
 - exact (prior 2173%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (43 <= level)%coq_nat; lia))).
 - exact (prior 2175%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (44 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2177 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(46 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::31] 14 final=Some (Gval (Fuint 5) (global_word_2177 v)).
Proof.
 eapply global_node_2177_step.
 - exact (prior 2176%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (45 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2178 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(47 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::31] 15 final=Some (Gval (Fuint 1) (global_word_2178 v)).
Proof.
 eapply global_node_2178_step.
 - exact (prior 2177%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (46 <= level)%coq_nat; lia))).
 - exact (prior 2172%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (39 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2179 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::31] 1 final=Some (Gval (Fuint 1) (global_word_2179 v)).
Proof.
 apply (global_sync_2179_link invalid snapshot final v); [eapply global_progress_1359; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_2180 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::31] 16 final=Some (Gval (Fuint 1) (global_word_2180 v)).
Proof.
 eapply global_node_2180_step.
 - exact (prior 2179%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2181 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::31] 17 final=Some (Gval (Fuint 1) (global_word_2181 v)).
Proof.
 eapply global_node_2181_step.
 - exact (prior 2180%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2182 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(48 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::31] 18 final=Some (Gval (Fuint 1) (global_word_2182 v)).
Proof.
 eapply global_node_2182_step.
 - exact (prior 2178%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (47 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2183 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::31] 0 final=Some (Gval Fclock (global_word_2183 v)).
Proof.
 apply (global_sync_2183_link invalid snapshot final v); [eapply global_progress_1358; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_2184 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(37 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::32] 6 final=Some (Gval (Fuint 4) (global_word_2184 v)).
Proof.
 eapply global_node_2184_step.
 - exact (prior 1167%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (36 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2185 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(37 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::32] 7 final=Some (Gval (Fuint 4) (global_word_2185 v)).
Proof.
 eapply global_node_2185_step.
 - exact (prior 1170%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (36 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2186 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(38 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::32] 8 final=Some (Gval (Fuint 5) (global_word_2186 v)).
Proof.
 eapply global_node_2186_step.
 - exact (prior 2184%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact (prior 2185%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2187 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(39 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::32] 9 final=Some (Gval (Fuint 4) (global_word_2187 v)).
Proof.
 eapply global_node_2187_step.
 - exact (prior 2186%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (38 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2188 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(43 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::32] 10 final=Some (Gval (Fuint 4) (global_word_2188 v)).
Proof.
 eapply global_node_2188_step.
 - exact (prior 1177%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (42 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2189 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(43 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::32] 11 final=Some (Gval (Fuint 4) (global_word_2189 v)).
Proof.
 eapply global_node_2189_step.
 - exact (prior 1181%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (42 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2190 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(44 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::32] 12 final=Some (Gval (Fuint 5) (global_word_2190 v)).
Proof.
 eapply global_node_2190_step.
 - exact (prior 2189%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (43 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2191 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(45 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::32] 13 final=Some (Gval (Fuint 6) (global_word_2191 v)).
Proof.
 eapply global_node_2191_step.
 - exact (prior 2188%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (43 <= level)%coq_nat; lia))).
 - exact (prior 2190%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (44 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2192 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(46 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::32] 14 final=Some (Gval (Fuint 5) (global_word_2192 v)).
Proof.
 eapply global_node_2192_step.
 - exact (prior 2191%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (45 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2193 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(47 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::32] 15 final=Some (Gval (Fuint 1) (global_word_2193 v)).
Proof.
 eapply global_node_2193_step.
 - exact (prior 2192%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (46 <= level)%coq_nat; lia))).
 - exact (prior 2187%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (39 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2194 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::32] 1 final=Some (Gval (Fuint 1) (global_word_2194 v)).
Proof.
 apply (global_sync_2194_link invalid snapshot final v); [eapply global_progress_1361; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_2195 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::32] 16 final=Some (Gval (Fuint 1) (global_word_2195 v)).
Proof.
 eapply global_node_2195_step.
 - exact (prior 2194%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2196 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::32] 17 final=Some (Gval (Fuint 1) (global_word_2196 v)).
Proof.
 eapply global_node_2196_step.
 - exact (prior 2195%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2197 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(48 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::32] 18 final=Some (Gval (Fuint 1) (global_word_2197 v)).
Proof.
 eapply global_node_2197_step.
 - exact (prior 2193%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (47 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2198 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::32] 0 final=Some (Gval Fclock (global_word_2198 v)).
Proof.
 apply (global_sync_2198_link invalid snapshot final v); [eapply global_progress_1360; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_2199 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 7 final=Some (Gval (Fuint 4) (global_word_2199 v)).
Proof.
 eapply global_node_2199_step.
 - exact (prior 1188%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
