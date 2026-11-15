From Coq Require Import NArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import HierarchyFacts PortFieldFacts.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalWidthFacts GlobalNodeSteps GlobalFieldSteps GlobalScalarSteps GlobalSyncSteps GlobalLeaves.
Local Open Scope N_scope.
From SmallMultiplier Require Import GlobalProgressTypes.
From SmallMultiplier Require Export GlobalProgress10.
Lemma global_progress_2200 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(20 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 8 final=Some (Gval (Fuint 4) (global_word_2200 v)).
Proof.
 eapply global_node_2200_step.
 - exact (prior 1191%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (19 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2201 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(37 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 9 final=Some (Gval (Fuint 4) (global_word_2201 v)).
Proof.
 eapply global_node_2201_step.
 - exact (prior 1185%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (36 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2202 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(21 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 10 final=Some (Gval (Fuint 5) (global_word_2202 v)).
Proof.
 eapply global_node_2202_step.
 - exact (prior 2199%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 2200%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (20 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2203 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(22 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 11 final=Some (Gval (Fuint 4) (global_word_2203 v)).
Proof.
 eapply global_node_2203_step.
 - exact (prior 2202%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (21 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2204 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(38 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 12 final=Some (Gval (Fuint 5) (global_word_2204 v)).
Proof.
 eapply global_node_2204_step.
 - exact (prior 2203%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (22 <= level)%coq_nat; lia))).
 - exact (prior 2201%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (37 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2205 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(39 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 13 final=Some (Gval (Fuint 4) (global_word_2205 v)).
Proof.
 eapply global_node_2205_step.
 - exact (prior 2204%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (38 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2206 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(44 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 14 final=Some (Gval (Fuint 4) (global_word_2206 v)).
Proof.
 eapply global_node_2206_step.
 - exact (prior 1201%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (43 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2207 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(44 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 15 final=Some (Gval (Fuint 4) (global_word_2207 v)).
Proof.
 eapply global_node_2207_step.
 - exact (prior 1205%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (43 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2208 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(45 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 16 final=Some (Gval (Fuint 5) (global_word_2208 v)).
Proof.
 eapply global_node_2208_step.
 - exact (prior 2207%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (44 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2209 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(46 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 17 final=Some (Gval (Fuint 6) (global_word_2209 v)).
Proof.
 eapply global_node_2209_step.
 - exact (prior 2206%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (44 <= level)%coq_nat; lia))).
 - exact (prior 2208%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (45 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2210 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(47 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 18 final=Some (Gval (Fuint 5) (global_word_2210 v)).
Proof.
 eapply global_node_2210_step.
 - exact (prior 2209%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (46 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2211 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(48 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 19 final=Some (Gval (Fuint 1) (global_word_2211 v)).
Proof.
 eapply global_node_2211_step.
 - exact (prior 2205%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (39 <= level)%coq_nat; lia))).
 - exact (prior 2210%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (47 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2212 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 1 final=Some (Gval (Fuint 1) (global_word_2212 v)).
Proof.
 apply (global_sync_2212_link invalid snapshot final v); [eapply global_progress_1363; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_2213 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 20 final=Some (Gval (Fuint 1) (global_word_2213 v)).
Proof.
 eapply global_node_2213_step.
 - exact (prior 2212%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2214 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 21 final=Some (Gval (Fuint 1) (global_word_2214 v)).
Proof.
 eapply global_node_2214_step.
 - exact (prior 2213%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2215 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(49 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 22 final=Some (Gval (Fuint 1) (global_word_2215 v)).
Proof.
 eapply global_node_2215_step.
 - exact (prior 2211%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (48 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2216 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 0 final=Some (Gval Fclock (global_word_2216 v)).
Proof.
 apply (global_sync_2216_link invalid snapshot final v); [eapply global_progress_1362; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_2217 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::34] 6 final=Some (Gval (Fuint 4) (global_word_2217 v)).
Proof.
 eapply global_node_2217_step.
 - exact (prior 1209%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (12 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2218 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::34] 7 final=Some (Gval (Fuint 4) (global_word_2218 v)).
Proof.
 eapply global_node_2218_step.
 - exact (prior 1212%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2219 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::34] 8 final=Some (Gval (Fuint 5) (global_word_2219 v)).
Proof.
 eapply global_node_2219_step.
 - exact (prior 2217%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact (prior 2218%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2220 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(17 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::34] 9 final=Some (Gval (Fuint 4) (global_word_2220 v)).
Proof.
 eapply global_node_2220_step.
 - exact (prior 2219%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2221 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(21 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::34] 10 final=Some (Gval (Fuint 4) (global_word_2221 v)).
Proof.
 eapply global_node_2221_step.
 - exact (prior 1219%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (20 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2222 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(21 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::34] 11 final=Some (Gval (Fuint 4) (global_word_2222 v)).
Proof.
 eapply global_node_2222_step.
 - exact (prior 1223%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (20 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2223 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(22 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::34] 12 final=Some (Gval (Fuint 5) (global_word_2223 v)).
Proof.
 eapply global_node_2223_step.
 - exact (prior 2222%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (21 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2224 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(23 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::34] 13 final=Some (Gval (Fuint 6) (global_word_2224 v)).
Proof.
 eapply global_node_2224_step.
 - exact (prior 2221%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (21 <= level)%coq_nat; lia))).
 - exact (prior 2223%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (22 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2225 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(24 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::34] 14 final=Some (Gval (Fuint 5) (global_word_2225 v)).
Proof.
 eapply global_node_2225_step.
 - exact (prior 2224%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (23 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2226 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(25 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::34] 15 final=Some (Gval (Fuint 1) (global_word_2226 v)).
Proof.
 eapply global_node_2226_step.
 - exact (prior 2225%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (24 <= level)%coq_nat; lia))).
 - exact (prior 2220%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2227 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::34] 1 final=Some (Gval (Fuint 1) (global_word_2227 v)).
Proof.
 apply (global_sync_2227_link invalid snapshot final v); [eapply global_progress_1365; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_2228 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::34] 16 final=Some (Gval (Fuint 1) (global_word_2228 v)).
Proof.
 eapply global_node_2228_step.
 - exact (prior 2227%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2229 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::34] 17 final=Some (Gval (Fuint 1) (global_word_2229 v)).
Proof.
 eapply global_node_2229_step.
 - exact (prior 2228%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2230 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(26 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::34] 18 final=Some (Gval (Fuint 1) (global_word_2230 v)).
Proof.
 eapply global_node_2230_step.
 - exact (prior 2226%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (25 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2231 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::34] 0 final=Some (Gval Fclock (global_word_2231 v)).
Proof.
 apply (global_sync_2231_link invalid snapshot final v); [eapply global_progress_1364; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_2232 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::35] 6 final=Some (Gval (Fuint 4) (global_word_2232 v)).
Proof.
 eapply global_node_2232_step.
 - exact (prior 1227%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (12 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2233 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::35] 7 final=Some (Gval (Fuint 4) (global_word_2233 v)).
Proof.
 eapply global_node_2233_step.
 - exact (prior 1230%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (12 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2234 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::35] 8 final=Some (Gval (Fuint 5) (global_word_2234 v)).
Proof.
 eapply global_node_2234_step.
 - exact (prior 2232%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact (prior 2233%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2235 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::35] 9 final=Some (Gval (Fuint 4) (global_word_2235 v)).
Proof.
 eapply global_node_2235_step.
 - exact (prior 2234%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2236 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(19 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::35] 10 final=Some (Gval (Fuint 4) (global_word_2236 v)).
Proof.
 eapply global_node_2236_step.
 - exact (prior 1237%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2237 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(19 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::35] 11 final=Some (Gval (Fuint 4) (global_word_2237 v)).
Proof.
 eapply global_node_2237_step.
 - exact (prior 1241%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2238 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(20 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::35] 12 final=Some (Gval (Fuint 5) (global_word_2238 v)).
Proof.
 eapply global_node_2238_step.
 - exact (prior 2237%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (19 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2239 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(21 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::35] 13 final=Some (Gval (Fuint 6) (global_word_2239 v)).
Proof.
 eapply global_node_2239_step.
 - exact (prior 2236%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (19 <= level)%coq_nat; lia))).
 - exact (prior 2238%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (20 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2240 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(22 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::35] 14 final=Some (Gval (Fuint 5) (global_word_2240 v)).
Proof.
 eapply global_node_2240_step.
 - exact (prior 2239%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (21 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2241 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(23 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::35] 15 final=Some (Gval (Fuint 1) (global_word_2241 v)).
Proof.
 eapply global_node_2241_step.
 - exact (prior 2240%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (22 <= level)%coq_nat; lia))).
 - exact (prior 2235%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2242 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::35] 1 final=Some (Gval (Fuint 1) (global_word_2242 v)).
Proof.
 apply (global_sync_2242_link invalid snapshot final v); [eapply global_progress_1367; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_2243 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::35] 16 final=Some (Gval (Fuint 1) (global_word_2243 v)).
Proof.
 eapply global_node_2243_step.
 - exact (prior 2242%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2244 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::35] 17 final=Some (Gval (Fuint 1) (global_word_2244 v)).
Proof.
 eapply global_node_2244_step.
 - exact (prior 2243%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2245 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(24 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::35] 18 final=Some (Gval (Fuint 1) (global_word_2245 v)).
Proof.
 eapply global_node_2245_step.
 - exact (prior 2241%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (23 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2246 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::35] 0 final=Some (Gval Fclock (global_word_2246 v)).
Proof.
 apply (global_sync_2246_link invalid snapshot final v); [eapply global_progress_1366; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_2247 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::36] 6 final=Some (Gval (Fuint 4) (global_word_2247 v)).
Proof.
 eapply global_node_2247_step.
 - exact (prior 1245%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2248 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::36] 7 final=Some (Gval (Fuint 4) (global_word_2248 v)).
Proof.
 eapply global_node_2248_step.
 - exact (prior 1248%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (12 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2249 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::36] 8 final=Some (Gval (Fuint 5) (global_word_2249 v)).
Proof.
 eapply global_node_2249_step.
 - exact (prior 2247%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact (prior 2248%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2250 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::36] 9 final=Some (Gval (Fuint 4) (global_word_2250 v)).
Proof.
 eapply global_node_2250_step.
 - exact (prior 2249%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2251 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(19 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::36] 10 final=Some (Gval (Fuint 4) (global_word_2251 v)).
Proof.
 eapply global_node_2251_step.
 - exact (prior 1255%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2252 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(19 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::36] 11 final=Some (Gval (Fuint 4) (global_word_2252 v)).
Proof.
 eapply global_node_2252_step.
 - exact (prior 1259%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2253 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(20 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::36] 12 final=Some (Gval (Fuint 5) (global_word_2253 v)).
Proof.
 eapply global_node_2253_step.
 - exact (prior 2252%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (19 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2254 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(21 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::36] 13 final=Some (Gval (Fuint 6) (global_word_2254 v)).
Proof.
 eapply global_node_2254_step.
 - exact (prior 2251%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (19 <= level)%coq_nat; lia))).
 - exact (prior 2253%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (20 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2255 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(22 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::36] 14 final=Some (Gval (Fuint 5) (global_word_2255 v)).
Proof.
 eapply global_node_2255_step.
 - exact (prior 2254%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (21 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2256 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(23 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::36] 15 final=Some (Gval (Fuint 1) (global_word_2256 v)).
Proof.
 eapply global_node_2256_step.
 - exact (prior 2255%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (22 <= level)%coq_nat; lia))).
 - exact (prior 2250%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2257 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::36] 1 final=Some (Gval (Fuint 1) (global_word_2257 v)).
Proof.
 apply (global_sync_2257_link invalid snapshot final v); [eapply global_progress_1369; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_2258 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::36] 16 final=Some (Gval (Fuint 1) (global_word_2258 v)).
Proof.
 eapply global_node_2258_step.
 - exact (prior 2257%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2259 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::36] 17 final=Some (Gval (Fuint 1) (global_word_2259 v)).
Proof.
 eapply global_node_2259_step.
 - exact (prior 2258%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2260 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(24 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::36] 18 final=Some (Gval (Fuint 1) (global_word_2260 v)).
Proof.
 eapply global_node_2260_step.
 - exact (prior 2256%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (23 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_2261 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::36] 0 final=Some (Gval Fclock (global_word_2261 v)).
Proof.
 apply (global_sync_2261_link invalid snapshot final v); [eapply global_progress_1368; try eassumption; lia|exact ran].
Qed.
