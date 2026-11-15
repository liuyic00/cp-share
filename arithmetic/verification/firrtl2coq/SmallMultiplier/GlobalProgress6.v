From Coq Require Import NArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import HierarchyFacts PortFieldFacts.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalWidthFacts GlobalNodeSteps GlobalFieldSteps GlobalScalarSteps GlobalSyncSteps GlobalLeaves.
Local Open Scope N_scope.
From SmallMultiplier Require Import GlobalProgressTypes.
From SmallMultiplier Require Export GlobalProgress5.
Lemma global_progress_1200 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(42 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 33 final=Some (Gval (Fuint 1) (global_word_1200 v)).
Proof.
 eapply global_node_1200_step.
 - exact (prior 1199%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (41 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_1201.
Lemma global_connect_1201_alias v : global_word_1201 v = global_word_1200 v.
Proof. unfold global_word_1201, global_closed_1201, global_expr_1201, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_1201.
Lemma global_progress_1201 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(43 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 5 final=Some (Gval (Fuint 1) (global_word_1201 v)).
Proof.
 have Typed := types 1201%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_1201_step.
 - exact (prior 1200%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (42 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_1201_alias. apply adapt_uint_same. exact (global_size_1200 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1202 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(44 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 33 5 final=Some (Gval (Fuint 1) (global_word_1202 v)).
Proof.
 apply (global_sync_1202_link invalid snapshot final v); [eapply global_progress_1201; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1203 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(45 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 365 final=Some (Gval (Fuint 1) (global_word_1203 v)).
Proof.
 eapply global_node_1203_step.
 - exact (prior 1202%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (44 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1204 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(42 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 34 final=Some (Gval (Fuint 1) (global_word_1204 v)).
Proof.
 eapply global_node_1204_step.
 - exact (prior 1199%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (41 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_1205.
Lemma global_connect_1205_alias v : global_word_1205 v = global_word_1204 v.
Proof. unfold global_word_1205, global_closed_1205, global_expr_1205, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_1205.
Lemma global_progress_1205 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(43 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 6 final=Some (Gval (Fuint 1) (global_word_1205 v)).
Proof.
 have Typed := types 1205%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_1205_step.
 - exact (prior 1204%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (42 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_1205_alias. apply adapt_uint_same. exact (global_size_1204 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1206 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(44 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 33 6 final=Some (Gval (Fuint 1) (global_word_1206 v)).
Proof.
 apply (global_sync_1206_link invalid snapshot final v); [eapply global_progress_1205; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1207 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(45 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 366 final=Some (Gval (Fuint 1) (global_word_1207 v)).
Proof.
 eapply global_node_1207_step.
 - exact (prior 1206%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (44 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1208 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(11 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 34 2 final=Some (Gval (Fuint 1) (global_word_1208 v)).
Proof.
 have Typed := types 1208%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1208_step.
 - exact (prior 951%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (10 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1208 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1209 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(12 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::34] 2 final=Some (Gval (Fuint 1) (global_word_1209 v)).
Proof.
 apply (global_sync_1209_link invalid snapshot final v); [eapply global_progress_1208; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1210 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::34] 19 final=Some (Gval (Fuint 1) (global_word_1210 v)).
Proof.
 eapply global_node_1210_step.
 - exact (prior 1209%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (12 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1211 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 34 3 final=Some (Gval (Fuint 1) (global_word_1211 v)).
Proof.
 have Typed := types 1211%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1211_step.
 - exact (prior 937%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (12 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1211 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1212 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::34] 3 final=Some (Gval (Fuint 1) (global_word_1212 v)).
Proof.
 apply (global_sync_1212_link invalid snapshot final v); [eapply global_progress_1211; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1213 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::34] 20 final=Some (Gval (Fuint 1) (global_word_1213 v)).
Proof.
 eapply global_node_1213_step.
 - exact (prior 1212%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1214 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::34] 21 final=Some (Gval (Fuint 1) (global_word_1214 v)).
Proof.
 eapply global_node_1214_step.
 - exact (prior 1210%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact (prior 1213%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1215 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::34] 22 final=Some (Gval (Fuint 1) (global_word_1215 v)).
Proof.
 eapply global_node_1215_step.
 - exact (prior 1210%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact (prior 1213%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1216 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(17 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::34] 23 final=Some (Gval (Fuint 2) (global_word_1216 v)).
Proof.
 eapply global_node_1216_step.
 - exact (prior 1214%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact (prior 1215%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1217 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::34] 24 final=Some (Gval (Fuint 2) (global_word_1217 v)).
Proof.
 eapply global_node_1217_step.
 - exact (prior 1216%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1218 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(19 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::34] 25 final=Some (Gval (Fuint 1) (global_word_1218 v)).
Proof.
 eapply global_node_1218_step.
 - exact (prior 1217%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_1219.
Lemma global_connect_1219_alias v : global_word_1219 v = global_word_1218 v.
Proof. unfold global_word_1219, global_closed_1219, global_expr_1219, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_1219.
Lemma global_progress_1219 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(20 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::34] 4 final=Some (Gval (Fuint 1) (global_word_1219 v)).
Proof.
 have Typed := types 1219%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_1219_step.
 - exact (prior 1218%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (19 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_1219_alias. apply adapt_uint_same. exact (global_size_1218 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1220 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(21 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 34 4 final=Some (Gval (Fuint 1) (global_word_1220 v)).
Proof.
 apply (global_sync_1220_link invalid snapshot final v); [eapply global_progress_1219; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1221 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(22 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 367 final=Some (Gval (Fuint 1) (global_word_1221 v)).
Proof.
 eapply global_node_1221_step.
 - exact (prior 1220%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (21 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1222 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(19 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::34] 26 final=Some (Gval (Fuint 1) (global_word_1222 v)).
Proof.
 eapply global_node_1222_step.
 - exact (prior 1217%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_1223.
Lemma global_connect_1223_alias v : global_word_1223 v = global_word_1222 v.
Proof. unfold global_word_1223, global_closed_1223, global_expr_1223, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_1223.
Lemma global_progress_1223 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(20 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::34] 5 final=Some (Gval (Fuint 1) (global_word_1223 v)).
Proof.
 have Typed := types 1223%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_1223_step.
 - exact (prior 1222%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (19 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_1223_alias. apply adapt_uint_same. exact (global_size_1222 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1224 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(21 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 34 5 final=Some (Gval (Fuint 1) (global_word_1224 v)).
Proof.
 apply (global_sync_1224_link invalid snapshot final v); [eapply global_progress_1223; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1225 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(22 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 368 final=Some (Gval (Fuint 1) (global_word_1225 v)).
Proof.
 eapply global_node_1225_step.
 - exact (prior 1224%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (21 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1226 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(11 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 35 2 final=Some (Gval (Fuint 1) (global_word_1226 v)).
Proof.
 have Typed := types 1226%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1226_step.
 - exact (prior 969%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (10 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1226 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1227 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(12 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::35] 2 final=Some (Gval (Fuint 1) (global_word_1227 v)).
Proof.
 apply (global_sync_1227_link invalid snapshot final v); [eapply global_progress_1226; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1228 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::35] 19 final=Some (Gval (Fuint 1) (global_word_1228 v)).
Proof.
 eapply global_node_1228_step.
 - exact (prior 1227%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (12 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1229 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(11 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 35 3 final=Some (Gval (Fuint 1) (global_word_1229 v)).
Proof.
 have Typed := types 1229%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1229_step.
 - exact (prior 955%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (10 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1229 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1230 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(12 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::35] 3 final=Some (Gval (Fuint 1) (global_word_1230 v)).
Proof.
 apply (global_sync_1230_link invalid snapshot final v); [eapply global_progress_1229; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1231 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::35] 20 final=Some (Gval (Fuint 1) (global_word_1231 v)).
Proof.
 eapply global_node_1231_step.
 - exact (prior 1230%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (12 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1232 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::35] 21 final=Some (Gval (Fuint 1) (global_word_1232 v)).
Proof.
 eapply global_node_1232_step.
 - exact (prior 1228%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact (prior 1231%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1233 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::35] 22 final=Some (Gval (Fuint 1) (global_word_1233 v)).
Proof.
 eapply global_node_1233_step.
 - exact (prior 1228%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact (prior 1231%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1234 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::35] 23 final=Some (Gval (Fuint 2) (global_word_1234 v)).
Proof.
 eapply global_node_1234_step.
 - exact (prior 1232%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact (prior 1233%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1235 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::35] 24 final=Some (Gval (Fuint 2) (global_word_1235 v)).
Proof.
 eapply global_node_1235_step.
 - exact (prior 1234%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1236 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(17 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::35] 25 final=Some (Gval (Fuint 1) (global_word_1236 v)).
Proof.
 eapply global_node_1236_step.
 - exact (prior 1235%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_1237.
Lemma global_connect_1237_alias v : global_word_1237 v = global_word_1236 v.
Proof. unfold global_word_1237, global_closed_1237, global_expr_1237, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_1237.
Lemma global_progress_1237 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::35] 4 final=Some (Gval (Fuint 1) (global_word_1237 v)).
Proof.
 have Typed := types 1237%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_1237_step.
 - exact (prior 1236%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_1237_alias. apply adapt_uint_same. exact (global_size_1236 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1238 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(19 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 35 4 final=Some (Gval (Fuint 1) (global_word_1238 v)).
Proof.
 apply (global_sync_1238_link invalid snapshot final v); [eapply global_progress_1237; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1239 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(20 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 369 final=Some (Gval (Fuint 1) (global_word_1239 v)).
Proof.
 eapply global_node_1239_step.
 - exact (prior 1238%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (19 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1240 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(17 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::35] 26 final=Some (Gval (Fuint 1) (global_word_1240 v)).
Proof.
 eapply global_node_1240_step.
 - exact (prior 1235%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_1241.
Lemma global_connect_1241_alias v : global_word_1241 v = global_word_1240 v.
Proof. unfold global_word_1241, global_closed_1241, global_expr_1241, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_1241.
Lemma global_progress_1241 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::35] 5 final=Some (Gval (Fuint 1) (global_word_1241 v)).
Proof.
 have Typed := types 1241%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_1241_step.
 - exact (prior 1240%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_1241_alias. apply adapt_uint_same. exact (global_size_1240 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1242 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(19 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 35 5 final=Some (Gval (Fuint 1) (global_word_1242 v)).
Proof.
 apply (global_sync_1242_link invalid snapshot final v); [eapply global_progress_1241; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1243 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(20 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 370 final=Some (Gval (Fuint 1) (global_word_1243 v)).
Proof.
 eapply global_node_1243_step.
 - exact (prior 1242%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (19 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1244 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 36 2 final=Some (Gval (Fuint 1) (global_word_1244 v)).
Proof.
 have Typed := types 1244%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1244_step.
 - exact (prior 55%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1244 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1245 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::36] 2 final=Some (Gval (Fuint 1) (global_word_1245 v)).
Proof.
 apply (global_sync_1245_link invalid snapshot final v); [eapply global_progress_1244; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1246 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::36] 19 final=Some (Gval (Fuint 1) (global_word_1246 v)).
Proof.
 eapply global_node_1246_step.
 - exact (prior 1245%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1247 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(11 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 36 3 final=Some (Gval (Fuint 1) (global_word_1247 v)).
Proof.
 have Typed := types 1247%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1247_step.
 - exact (prior 973%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (10 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1247 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1248 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(12 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::36] 3 final=Some (Gval (Fuint 1) (global_word_1248 v)).
Proof.
 apply (global_sync_1248_link invalid snapshot final v); [eapply global_progress_1247; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1249 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::36] 20 final=Some (Gval (Fuint 1) (global_word_1249 v)).
Proof.
 eapply global_node_1249_step.
 - exact (prior 1248%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (12 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1250 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::36] 21 final=Some (Gval (Fuint 1) (global_word_1250 v)).
Proof.
 eapply global_node_1250_step.
 - exact (prior 1246%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact (prior 1249%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1251 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::36] 22 final=Some (Gval (Fuint 1) (global_word_1251 v)).
Proof.
 eapply global_node_1251_step.
 - exact (prior 1246%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact (prior 1249%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1252 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::36] 23 final=Some (Gval (Fuint 2) (global_word_1252 v)).
Proof.
 eapply global_node_1252_step.
 - exact (prior 1250%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact (prior 1251%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1253 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::36] 24 final=Some (Gval (Fuint 2) (global_word_1253 v)).
Proof.
 eapply global_node_1253_step.
 - exact (prior 1252%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1254 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(17 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::36] 25 final=Some (Gval (Fuint 1) (global_word_1254 v)).
Proof.
 eapply global_node_1254_step.
 - exact (prior 1253%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_1255.
Lemma global_connect_1255_alias v : global_word_1255 v = global_word_1254 v.
Proof. unfold global_word_1255, global_closed_1255, global_expr_1255, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_1255.
Lemma global_progress_1255 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::36] 4 final=Some (Gval (Fuint 1) (global_word_1255 v)).
Proof.
 have Typed := types 1255%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_1255_step.
 - exact (prior 1254%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_1255_alias. apply adapt_uint_same. exact (global_size_1254 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1256 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(19 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 36 4 final=Some (Gval (Fuint 1) (global_word_1256 v)).
Proof.
 apply (global_sync_1256_link invalid snapshot final v); [eapply global_progress_1255; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1257 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(20 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 371 final=Some (Gval (Fuint 1) (global_word_1257 v)).
Proof.
 eapply global_node_1257_step.
 - exact (prior 1256%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (19 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1258 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(17 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::36] 26 final=Some (Gval (Fuint 1) (global_word_1258 v)).
Proof.
 eapply global_node_1258_step.
 - exact (prior 1253%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_1259.
Lemma global_connect_1259_alias v : global_word_1259 v = global_word_1258 v.
Proof. unfold global_word_1259, global_closed_1259, global_expr_1259, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_1259.
Lemma global_progress_1259 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::36] 5 final=Some (Gval (Fuint 1) (global_word_1259 v)).
Proof.
 have Typed := types 1259%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_1259_step.
 - exact (prior 1258%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_1259_alias. apply adapt_uint_same. exact (global_size_1258 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1260 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(19 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 36 5 final=Some (Gval (Fuint 1) (global_word_1260 v)).
Proof.
 apply (global_sync_1260_link invalid snapshot final v); [eapply global_progress_1259; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1261 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(20 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 372 final=Some (Gval (Fuint 1) (global_word_1261 v)).
Proof.
 eapply global_node_1261_step.
 - exact (prior 1260%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (19 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1262 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(21 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 373 final=Some (Gval (Fuint 2) (global_word_1262 v)).
Proof.
 eapply global_node_1262_step.
 - exact (prior 291%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (10 <= level)%coq_nat; lia))).
 - exact (prior 987%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (20 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1263 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(23 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 374 final=Some (Gval (Fuint 2) (global_word_1263 v)).
Proof.
 eapply global_node_1263_step.
 - exact (prior 1005%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (22 <= level)%coq_nat; lia))).
 - exact (prior 1023%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (22 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1264 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(24 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 375 final=Some (Gval (Fuint 4) (global_word_1264 v)).
Proof.
 eapply global_node_1264_step.
 - exact (prior 1262%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (21 <= level)%coq_nat; lia))).
 - exact (prior 1263%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (23 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1265 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(45 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 376 final=Some (Gval (Fuint 2) (global_word_1265 v)).
Proof.
 eapply global_node_1265_step.
 - exact (prior 1041%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (39 <= level)%coq_nat; lia))).
 - exact (prior 1059%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (44 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1266 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(47 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 377 final=Some (Gval (Fuint 2) (global_word_1266 v)).
Proof.
 eapply global_node_1266_step.
 - exact (prior 1083%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (46 <= level)%coq_nat; lia))).
 - exact (prior 1107%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (46 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1267 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(48 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 378 final=Some (Gval (Fuint 4) (global_word_1267 v)).
Proof.
 eapply global_node_1267_step.
 - exact (prior 1265%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (45 <= level)%coq_nat; lia))).
 - exact (prior 1266%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (47 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1268 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(49 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 379 final=Some (Gval (Fuint 8) (global_word_1268 v)).
Proof.
 eapply global_node_1268_step.
 - exact (prior 1264%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (24 <= level)%coq_nat; lia))).
 - exact (prior 1267%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (48 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1269 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(45 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 380 final=Some (Gval (Fuint 2) (global_word_1269 v)).
Proof.
 eapply global_node_1269_step.
 - exact (prior 1125%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (44 <= level)%coq_nat; lia))).
 - exact (prior 1143%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (44 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1270 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(45 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 381 final=Some (Gval (Fuint 2) (global_word_1270 v)).
Proof.
 eapply global_node_1270_step.
 - exact (prior 1161%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (44 <= level)%coq_nat; lia))).
 - exact (prior 1179%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (44 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1271 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(46 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 382 final=Some (Gval (Fuint 4) (global_word_1271 v)).
Proof.
 eapply global_node_1271_step.
 - exact (prior 1269%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (45 <= level)%coq_nat; lia))).
 - exact (prior 1270%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (45 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1272 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(46 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 383 final=Some (Gval (Fuint 2) (global_word_1272 v)).
Proof.
 eapply global_node_1272_step.
 - exact (prior 1203%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (45 <= level)%coq_nat; lia))).
 - exact (prior 1221%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (22 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1273 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(21 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 384 final=Some (Gval (Fuint 2) (global_word_1273 v)).
Proof.
 eapply global_node_1273_step.
 - exact (prior 1239%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (20 <= level)%coq_nat; lia))).
 - exact (prior 1257%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (20 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1274 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(47 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 385 final=Some (Gval (Fuint 4) (global_word_1274 v)).
Proof.
 eapply global_node_1274_step.
 - exact (prior 1272%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (46 <= level)%coq_nat; lia))).
 - exact (prior 1273%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (21 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1275 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(48 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 386 final=Some (Gval (Fuint 8) (global_word_1275 v)).
Proof.
 eapply global_node_1275_step.
 - exact (prior 1271%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (46 <= level)%coq_nat; lia))).
 - exact (prior 1274%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (47 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1276 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(50 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 387 final=Some (Gval (Fuint 16) (global_word_1276 v)).
Proof.
 eapply global_node_1276_step.
 - exact (prior 1268%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (49 <= level)%coq_nat; lia))).
 - exact (prior 1275%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (48 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1277 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(23 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 388 final=Some (Gval (Fuint 2) (global_word_1277 v)).
Proof.
 eapply global_node_1277_step.
 - exact (prior 1009%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (22 <= level)%coq_nat; lia))).
 - exact (prior 1027%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (22 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1278 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(24 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 389 final=Some (Gval (Fuint 3) (global_word_1278 v)).
Proof.
 eapply global_node_1278_step.
 - exact (prior 991%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (20 <= level)%coq_nat; lia))).
 - exact (prior 1277%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (23 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1279 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(45 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 390 final=Some (Gval (Fuint 2) (global_word_1279 v)).
Proof.
 eapply global_node_1279_step.
 - exact (prior 1045%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (39 <= level)%coq_nat; lia))).
 - exact (prior 1063%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (44 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1280 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(47 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 391 final=Some (Gval (Fuint 2) (global_word_1280 v)).
Proof.
 eapply global_node_1280_step.
 - exact (prior 1087%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (46 <= level)%coq_nat; lia))).
 - exact (prior 1111%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (46 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1281 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(48 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 392 final=Some (Gval (Fuint 4) (global_word_1281 v)).
Proof.
 eapply global_node_1281_step.
 - exact (prior 1279%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (45 <= level)%coq_nat; lia))).
 - exact (prior 1280%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (47 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1282 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(49 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 393 final=Some (Gval (Fuint 7) (global_word_1282 v)).
Proof.
 eapply global_node_1282_step.
 - exact (prior 1278%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (24 <= level)%coq_nat; lia))).
 - exact (prior 1281%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (48 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1283 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(45 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 394 final=Some (Gval (Fuint 2) (global_word_1283 v)).
Proof.
 eapply global_node_1283_step.
 - exact (prior 1147%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (44 <= level)%coq_nat; lia))).
 - exact (prior 1165%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (44 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1284 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(46 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 395 final=Some (Gval (Fuint 3) (global_word_1284 v)).
Proof.
 eapply global_node_1284_step.
 - exact (prior 1129%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (44 <= level)%coq_nat; lia))).
 - exact (prior 1283%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (45 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1285 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(46 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 396 final=Some (Gval (Fuint 2) (global_word_1285 v)).
Proof.
 eapply global_node_1285_step.
 - exact (prior 1183%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (44 <= level)%coq_nat; lia))).
 - exact (prior 1207%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (45 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1286 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(23 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 397 final=Some (Gval (Fuint 2) (global_word_1286 v)).
Proof.
 eapply global_node_1286_step.
 - exact (prior 1225%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (22 <= level)%coq_nat; lia))).
 - exact (prior 1243%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (20 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1287 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(47 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 398 final=Some (Gval (Fuint 4) (global_word_1287 v)).
Proof.
 eapply global_node_1287_step.
 - exact (prior 1285%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (46 <= level)%coq_nat; lia))).
 - exact (prior 1286%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (23 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1288 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(48 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 399 final=Some (Gval (Fuint 7) (global_word_1288 v)).
Proof.
 eapply global_node_1288_step.
 - exact (prior 1284%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (46 <= level)%coq_nat; lia))).
 - exact (prior 1287%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (47 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1289 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(50 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 400 final=Some (Gval (Fuint 14) (global_word_1289 v)).
Proof.
 eapply global_node_1289_step.
 - exact (prior 1282%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (49 <= level)%coq_nat; lia))).
 - exact (prior 1288%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (48 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1290 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(51 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 401 final=Some (Gval (Fuint 16) (global_word_1290 v)).
Proof.
 eapply global_node_1290_step.
 - exact (prior 1289%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (50 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1291 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(52 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 402 final=Some (Gval (Fuint 17) (global_word_1291 v)).
Proof.
 eapply global_node_1291_step.
 - exact (prior 1276%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (50 <= level)%coq_nat; lia))).
 - exact (prior 1290%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (51 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1292 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(53 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 403 final=Some (Gval (Fuint 16) (global_word_1292 v)).
Proof.
 eapply global_node_1292_step.
 - exact (prior 1291%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (52 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1293 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 404 final=Some (Gval (Fsint 8) (global_word_1293 v)).
Proof.
 eapply global_node_1293_step.
 - exact (prior 2%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1294 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 405 final=Some (Gval (Fsint 8) (global_word_1294 v)).
Proof.
 eapply global_node_1294_step.
 - exact (prior 53%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1295 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 406 final=Some (Gval (Fsint 16) (global_word_1295 v)).
Proof.
 eapply global_node_1295_step.
 - exact (prior 1293%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (1 <= level)%coq_nat; lia))).
 - exact (prior 1294%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (1 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1296 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 407 final=Some (Gval (Fuint 16) (global_word_1296 v)).
Proof.
 eapply global_node_1296_step.
 - exact (prior 1295%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1297 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 409 final=Some (Gval (Fuint 16) (global_word_1297 v)).
Proof.
 eapply global_node_1297_step.
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 1296%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact (prior 57%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1298 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 411 final=Some (Gval (Fuint 1) (global_word_1298 v)).
Proof.
 eapply global_node_1298_step.
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 58%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_1299.
Lemma global_connect_1299_alias v : global_word_1299 v = global_word_1292 v.
Proof. unfold global_word_1299, global_closed_1299, global_expr_1299, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_1299.
Lemma global_progress_1299 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(54 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 6 final=Some (Gval (Fuint 16) (global_word_1299 v)).
Proof.
 have Typed := types 1299%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_1299_step.
 - exact (prior 1292%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (53 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_1299_alias. apply adapt_uint_same. exact (global_size_1292 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1300 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(55 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 412 final=Some (Gval (Fuint 1) (global_word_1300 v)).
Proof.
 eapply global_node_1300_step.
 - exact (prior 57%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 1299%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (54 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1301 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 413 final=Some (Gval (Fuint 1) (global_word_1301 v)).
Proof.
 eapply global_node_1301_step.
 - exact (prior 1%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1302 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 414 final=Some (Gval (Fuint 1) (global_word_1302 v)).
Proof.
 eapply global_node_1302_step.
 - exact (prior 1301%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (1 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1303 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(56 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 415 final=Some (Gval (Fuint 1) (global_word_1303 v)).
Proof.
 eapply global_node_1303_step.
 - exact (prior 1300%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (55 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1304 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 417 final=Some (Gval (Fuint 1) (global_word_1304 v)).
Proof.
 eapply global_node_1304_step.
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1305 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 418 final=Some (Gval (Fuint 1) (global_word_1305 v)).
Proof.
 eapply global_node_1305_step.
 - exact (prior 58%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 1304%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (1 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1306 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(55 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 420 final=Some (Gval (Fuint 1) (global_word_1306 v)).
Proof.
 eapply global_node_1306_step.
 - exact (prior 59%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 1299%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (54 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1307 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 421 final=Some (Gval (Fuint 1) (global_word_1307 v)).
Proof.
 eapply global_node_1307_step.
 - exact (prior 1%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1308 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 422 final=Some (Gval (Fuint 1) (global_word_1308 v)).
Proof.
 eapply global_node_1308_step.
 - exact (prior 1307%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (1 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1309 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(56 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 423 final=Some (Gval (Fuint 1) (global_word_1309 v)).
Proof.
 eapply global_node_1309_step.
 - exact (prior 1306%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (55 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1310 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 7 0 final=Some (Gval Fclock (global_word_1310 v)).
Proof.
 have Typed := types 1310%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1310_step.
 - exact (prior 0%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - reflexivity.
 - exact ran.
Qed.
Lemma global_progress_1311 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 7 1 final=Some (Gval (Fuint 1) (global_word_1311 v)).
Proof.
 have Typed := types 1311%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1311_step.
 - exact (prior 1%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1311 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1312 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 8 0 final=Some (Gval Fclock (global_word_1312 v)).
Proof.
 have Typed := types 1312%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1312_step.
 - exact (prior 0%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - reflexivity.
 - exact ran.
Qed.
Lemma global_progress_1313 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 8 1 final=Some (Gval (Fuint 1) (global_word_1313 v)).
Proof.
 have Typed := types 1313%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1313_step.
 - exact (prior 1%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1313 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1314 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 9 0 final=Some (Gval Fclock (global_word_1314 v)).
Proof.
 have Typed := types 1314%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1314_step.
 - exact (prior 0%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - reflexivity.
 - exact ran.
Qed.
Lemma global_progress_1315 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 9 1 final=Some (Gval (Fuint 1) (global_word_1315 v)).
Proof.
 have Typed := types 1315%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1315_step.
 - exact (prior 1%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1315 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1316 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 10 0 final=Some (Gval Fclock (global_word_1316 v)).
Proof.
 have Typed := types 1316%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1316_step.
 - exact (prior 0%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - reflexivity.
 - exact ran.
Qed.
Lemma global_progress_1317 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 10 1 final=Some (Gval (Fuint 1) (global_word_1317 v)).
Proof.
 have Typed := types 1317%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1317_step.
 - exact (prior 1%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1317 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1318 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 11 0 final=Some (Gval Fclock (global_word_1318 v)).
Proof.
 have Typed := types 1318%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1318_step.
 - exact (prior 0%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - reflexivity.
 - exact ran.
Qed.
Lemma global_progress_1319 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 11 1 final=Some (Gval (Fuint 1) (global_word_1319 v)).
Proof.
 have Typed := types 1319%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1319_step.
 - exact (prior 1%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1319 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1320 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 12 0 final=Some (Gval Fclock (global_word_1320 v)).
Proof.
 have Typed := types 1320%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1320_step.
 - exact (prior 0%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - reflexivity.
 - exact ran.
Qed.
Lemma global_progress_1321 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 12 1 final=Some (Gval (Fuint 1) (global_word_1321 v)).
Proof.
 have Typed := types 1321%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1321_step.
 - exact (prior 1%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1321 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1322 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 13 0 final=Some (Gval Fclock (global_word_1322 v)).
Proof.
 have Typed := types 1322%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1322_step.
 - exact (prior 0%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - reflexivity.
 - exact ran.
Qed.
Lemma global_progress_1323 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 13 1 final=Some (Gval (Fuint 1) (global_word_1323 v)).
Proof.
 have Typed := types 1323%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1323_step.
 - exact (prior 1%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1323 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1324 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 14 0 final=Some (Gval Fclock (global_word_1324 v)).
Proof.
 have Typed := types 1324%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1324_step.
 - exact (prior 0%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - reflexivity.
 - exact ran.
Qed.
Lemma global_progress_1325 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 14 1 final=Some (Gval (Fuint 1) (global_word_1325 v)).
Proof.
 have Typed := types 1325%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1325_step.
 - exact (prior 1%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1325 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1326 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 15 0 final=Some (Gval Fclock (global_word_1326 v)).
Proof.
 have Typed := types 1326%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1326_step.
 - exact (prior 0%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - reflexivity.
 - exact ran.
Qed.
Lemma global_progress_1327 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 15 1 final=Some (Gval (Fuint 1) (global_word_1327 v)).
Proof.
 have Typed := types 1327%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1327_step.
 - exact (prior 1%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1327 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1328 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 16 0 final=Some (Gval Fclock (global_word_1328 v)).
Proof.
 have Typed := types 1328%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1328_step.
 - exact (prior 0%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - reflexivity.
 - exact ran.
Qed.
Lemma global_progress_1329 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 16 1 final=Some (Gval (Fuint 1) (global_word_1329 v)).
Proof.
 have Typed := types 1329%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1329_step.
 - exact (prior 1%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1329 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1330 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 17 0 final=Some (Gval Fclock (global_word_1330 v)).
Proof.
 have Typed := types 1330%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1330_step.
 - exact (prior 0%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - reflexivity.
 - exact ran.
Qed.
Lemma global_progress_1331 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 17 1 final=Some (Gval (Fuint 1) (global_word_1331 v)).
Proof.
 have Typed := types 1331%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1331_step.
 - exact (prior 1%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1331 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1332 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 18 0 final=Some (Gval Fclock (global_word_1332 v)).
Proof.
 have Typed := types 1332%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1332_step.
 - exact (prior 0%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - reflexivity.
 - exact ran.
Qed.
Lemma global_progress_1333 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 18 1 final=Some (Gval (Fuint 1) (global_word_1333 v)).
Proof.
 have Typed := types 1333%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1333_step.
 - exact (prior 1%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1333 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1334 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 19 0 final=Some (Gval Fclock (global_word_1334 v)).
Proof.
 have Typed := types 1334%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1334_step.
 - exact (prior 0%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - reflexivity.
 - exact ran.
Qed.
Lemma global_progress_1335 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 19 1 final=Some (Gval (Fuint 1) (global_word_1335 v)).
Proof.
 have Typed := types 1335%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1335_step.
 - exact (prior 1%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1335 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1336 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 20 0 final=Some (Gval Fclock (global_word_1336 v)).
Proof.
 have Typed := types 1336%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1336_step.
 - exact (prior 0%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - reflexivity.
 - exact ran.
Qed.
Lemma global_progress_1337 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 20 1 final=Some (Gval (Fuint 1) (global_word_1337 v)).
Proof.
 have Typed := types 1337%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1337_step.
 - exact (prior 1%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1337 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1338 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 21 0 final=Some (Gval Fclock (global_word_1338 v)).
Proof.
 have Typed := types 1338%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1338_step.
 - exact (prior 0%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - reflexivity.
 - exact ran.
Qed.
Lemma global_progress_1339 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 21 1 final=Some (Gval (Fuint 1) (global_word_1339 v)).
Proof.
 have Typed := types 1339%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1339_step.
 - exact (prior 1%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1339 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1340 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 22 0 final=Some (Gval Fclock (global_word_1340 v)).
Proof.
 have Typed := types 1340%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1340_step.
 - exact (prior 0%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - reflexivity.
 - exact ran.
Qed.
Lemma global_progress_1341 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 22 1 final=Some (Gval (Fuint 1) (global_word_1341 v)).
Proof.
 have Typed := types 1341%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1341_step.
 - exact (prior 1%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1341 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1342 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 23 0 final=Some (Gval Fclock (global_word_1342 v)).
Proof.
 have Typed := types 1342%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1342_step.
 - exact (prior 0%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - reflexivity.
 - exact ran.
Qed.
Lemma global_progress_1343 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 23 1 final=Some (Gval (Fuint 1) (global_word_1343 v)).
Proof.
 have Typed := types 1343%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1343_step.
 - exact (prior 1%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1343 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1344 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 24 0 final=Some (Gval Fclock (global_word_1344 v)).
Proof.
 have Typed := types 1344%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1344_step.
 - exact (prior 0%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - reflexivity.
 - exact ran.
Qed.
Lemma global_progress_1345 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 24 1 final=Some (Gval (Fuint 1) (global_word_1345 v)).
Proof.
 have Typed := types 1345%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1345_step.
 - exact (prior 1%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1345 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1346 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 25 0 final=Some (Gval Fclock (global_word_1346 v)).
Proof.
 have Typed := types 1346%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1346_step.
 - exact (prior 0%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - reflexivity.
 - exact ran.
Qed.
Lemma global_progress_1347 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 25 1 final=Some (Gval (Fuint 1) (global_word_1347 v)).
Proof.
 have Typed := types 1347%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1347_step.
 - exact (prior 1%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1347 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1348 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 26 0 final=Some (Gval Fclock (global_word_1348 v)).
Proof.
 have Typed := types 1348%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1348_step.
 - exact (prior 0%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - reflexivity.
 - exact ran.
Qed.
Lemma global_progress_1349 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 26 1 final=Some (Gval (Fuint 1) (global_word_1349 v)).
Proof.
 have Typed := types 1349%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1349_step.
 - exact (prior 1%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1349 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1350 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 27 0 final=Some (Gval Fclock (global_word_1350 v)).
Proof.
 have Typed := types 1350%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1350_step.
 - exact (prior 0%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - reflexivity.
 - exact ran.
Qed.
Lemma global_progress_1351 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 27 1 final=Some (Gval (Fuint 1) (global_word_1351 v)).
Proof.
 have Typed := types 1351%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1351_step.
 - exact (prior 1%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1351 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1352 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 28 0 final=Some (Gval Fclock (global_word_1352 v)).
Proof.
 have Typed := types 1352%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1352_step.
 - exact (prior 0%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - reflexivity.
 - exact ran.
Qed.
Lemma global_progress_1353 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 28 1 final=Some (Gval (Fuint 1) (global_word_1353 v)).
Proof.
 have Typed := types 1353%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1353_step.
 - exact (prior 1%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1353 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1354 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 29 0 final=Some (Gval Fclock (global_word_1354 v)).
Proof.
 have Typed := types 1354%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1354_step.
 - exact (prior 0%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - reflexivity.
 - exact ran.
Qed.
Lemma global_progress_1355 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 29 1 final=Some (Gval (Fuint 1) (global_word_1355 v)).
Proof.
 have Typed := types 1355%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1355_step.
 - exact (prior 1%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1355 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1356 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 30 0 final=Some (Gval Fclock (global_word_1356 v)).
Proof.
 have Typed := types 1356%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1356_step.
 - exact (prior 0%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - reflexivity.
 - exact ran.
Qed.
Lemma global_progress_1357 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 30 1 final=Some (Gval (Fuint 1) (global_word_1357 v)).
Proof.
 have Typed := types 1357%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1357_step.
 - exact (prior 1%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1357 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1358 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 31 0 final=Some (Gval Fclock (global_word_1358 v)).
Proof.
 have Typed := types 1358%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1358_step.
 - exact (prior 0%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - reflexivity.
 - exact ran.
Qed.
Lemma global_progress_1359 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 31 1 final=Some (Gval (Fuint 1) (global_word_1359 v)).
Proof.
 have Typed := types 1359%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1359_step.
 - exact (prior 1%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1359 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1360 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 32 0 final=Some (Gval Fclock (global_word_1360 v)).
Proof.
 have Typed := types 1360%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1360_step.
 - exact (prior 0%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - reflexivity.
 - exact ran.
Qed.
Lemma global_progress_1361 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 32 1 final=Some (Gval (Fuint 1) (global_word_1361 v)).
Proof.
 have Typed := types 1361%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1361_step.
 - exact (prior 1%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1361 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1362 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 33 0 final=Some (Gval Fclock (global_word_1362 v)).
Proof.
 have Typed := types 1362%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1362_step.
 - exact (prior 0%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - reflexivity.
 - exact ran.
Qed.
Lemma global_progress_1363 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 33 1 final=Some (Gval (Fuint 1) (global_word_1363 v)).
Proof.
 have Typed := types 1363%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1363_step.
 - exact (prior 1%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1363 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1364 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 34 0 final=Some (Gval Fclock (global_word_1364 v)).
Proof.
 have Typed := types 1364%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1364_step.
 - exact (prior 0%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - reflexivity.
 - exact ran.
Qed.
Lemma global_progress_1365 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 34 1 final=Some (Gval (Fuint 1) (global_word_1365 v)).
Proof.
 have Typed := types 1365%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1365_step.
 - exact (prior 1%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1365 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1366 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 35 0 final=Some (Gval Fclock (global_word_1366 v)).
Proof.
 have Typed := types 1366%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1366_step.
 - exact (prior 0%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - reflexivity.
 - exact ran.
Qed.
Lemma global_progress_1367 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 35 1 final=Some (Gval (Fuint 1) (global_word_1367 v)).
Proof.
 have Typed := types 1367%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1367_step.
 - exact (prior 1%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1367 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1368 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 36 0 final=Some (Gval Fclock (global_word_1368 v)).
Proof.
 have Typed := types 1368%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1368_step.
 - exact (prior 0%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - reflexivity.
 - exact ran.
Qed.
Lemma global_progress_1369 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 36 1 final=Some (Gval (Fuint 1) (global_word_1369 v)).
Proof.
 have Typed := types 1369%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_1369_step.
 - exact (prior 1%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_1369 v sizes).
 - exact ran.
Qed.
Lemma global_progress_1370 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::7] 6 final=Some (Gval (Fuint 4) (global_word_1370 v)).
Proof.
 eapply global_node_1370_step.
 - exact (prior 279%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1371 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::7] 7 final=Some (Gval (Fuint 4) (global_word_1371 v)).
Proof.
 eapply global_node_1371_step.
 - exact (prior 282%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1372 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::7] 8 final=Some (Gval (Fuint 5) (global_word_1372 v)).
Proof.
 eapply global_node_1372_step.
 - exact (prior 1370%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact (prior 1371%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1373 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::7] 9 final=Some (Gval (Fuint 4) (global_word_1373 v)).
Proof.
 eapply global_node_1373_step.
 - exact (prior 1372%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1374 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(9 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::7] 10 final=Some (Gval (Fuint 4) (global_word_1374 v)).
Proof.
 eapply global_node_1374_step.
 - exact (prior 289%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (8 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1375 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(9 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::7] 11 final=Some (Gval (Fuint 4) (global_word_1375 v)).
Proof.
 eapply global_node_1375_step.
 - exact (prior 293%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (8 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1376 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(10 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::7] 12 final=Some (Gval (Fuint 5) (global_word_1376 v)).
Proof.
 eapply global_node_1376_step.
 - exact (prior 1375%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (9 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1377 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(11 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::7] 13 final=Some (Gval (Fuint 6) (global_word_1377 v)).
Proof.
 eapply global_node_1377_step.
 - exact (prior 1374%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (9 <= level)%coq_nat; lia))).
 - exact (prior 1376%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (10 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1378 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(12 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::7] 14 final=Some (Gval (Fuint 5) (global_word_1378 v)).
Proof.
 eapply global_node_1378_step.
 - exact (prior 1377%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (11 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1379 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::7] 15 final=Some (Gval (Fuint 1) (global_word_1379 v)).
Proof.
 eapply global_node_1379_step.
 - exact (prior 1378%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (12 <= level)%coq_nat; lia))).
 - exact (prior 1373%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1380 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::7] 1 final=Some (Gval (Fuint 1) (global_word_1380 v)).
Proof.
 apply (global_sync_1380_link invalid snapshot final v); [eapply global_progress_1311; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1381 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::7] 16 final=Some (Gval (Fuint 1) (global_word_1381 v)).
Proof.
 eapply global_node_1381_step.
 - exact (prior 1380%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1382 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::7] 17 final=Some (Gval (Fuint 1) (global_word_1382 v)).
Proof.
 eapply global_node_1382_step.
 - exact (prior 1381%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1383 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::7] 18 final=Some (Gval (Fuint 1) (global_word_1383 v)).
Proof.
 eapply global_node_1383_step.
 - exact (prior 1379%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1384 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::7] 0 final=Some (Gval Fclock (global_word_1384 v)).
Proof.
 apply (global_sync_1384_link invalid snapshot final v); [eapply global_progress_1310; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1385 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::8] 6 final=Some (Gval (Fuint 4) (global_word_1385 v)).
Proof.
 eapply global_node_1385_step.
 - exact (prior 297%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1386 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::8] 7 final=Some (Gval (Fuint 4) (global_word_1386 v)).
Proof.
 eapply global_node_1386_step.
 - exact (prior 300%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1387 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::8] 8 final=Some (Gval (Fuint 5) (global_word_1387 v)).
Proof.
 eapply global_node_1387_step.
 - exact (prior 1385%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact (prior 1386%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1388 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::8] 9 final=Some (Gval (Fuint 4) (global_word_1388 v)).
Proof.
 eapply global_node_1388_step.
 - exact (prior 1387%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1389 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(9 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::8] 10 final=Some (Gval (Fuint 4) (global_word_1389 v)).
Proof.
 eapply global_node_1389_step.
 - exact (prior 307%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (8 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1390 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(9 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::8] 11 final=Some (Gval (Fuint 4) (global_word_1390 v)).
Proof.
 eapply global_node_1390_step.
 - exact (prior 311%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (8 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1391 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(10 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::8] 12 final=Some (Gval (Fuint 5) (global_word_1391 v)).
Proof.
 eapply global_node_1391_step.
 - exact (prior 1390%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (9 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1392 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(11 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::8] 13 final=Some (Gval (Fuint 6) (global_word_1392 v)).
Proof.
 eapply global_node_1392_step.
 - exact (prior 1389%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (9 <= level)%coq_nat; lia))).
 - exact (prior 1391%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (10 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1393 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(12 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::8] 14 final=Some (Gval (Fuint 5) (global_word_1393 v)).
Proof.
 eapply global_node_1393_step.
 - exact (prior 1392%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (11 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1394 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::8] 15 final=Some (Gval (Fuint 1) (global_word_1394 v)).
Proof.
 eapply global_node_1394_step.
 - exact (prior 1393%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (12 <= level)%coq_nat; lia))).
 - exact (prior 1388%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1395 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::8] 1 final=Some (Gval (Fuint 1) (global_word_1395 v)).
Proof.
 apply (global_sync_1395_link invalid snapshot final v); [eapply global_progress_1313; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_1396 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::8] 16 final=Some (Gval (Fuint 1) (global_word_1396 v)).
Proof.
 eapply global_node_1396_step.
 - exact (prior 1395%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1397 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::8] 17 final=Some (Gval (Fuint 1) (global_word_1397 v)).
Proof.
 eapply global_node_1397_step.
 - exact (prior 1396%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1398 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::8] 18 final=Some (Gval (Fuint 1) (global_word_1398 v)).
Proof.
 eapply global_node_1398_step.
 - exact (prior 1394%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_1399 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::8] 0 final=Some (Gval Fclock (global_word_1399 v)).
Proof.
 apply (global_sync_1399_link invalid snapshot final v); [eapply global_progress_1312; try eassumption; lia|exact ran].
Qed.
