From Coq Require Import NArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import HierarchyFacts PortFieldFacts.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalWidthFacts GlobalNodeSteps GlobalFieldSteps GlobalScalarSteps GlobalSyncSteps GlobalLeaves.
Local Open Scope N_scope.
From SmallMultiplier Require Import GlobalProgressTypes.
From SmallMultiplier Require Export GlobalProgress1.
Lemma global_progress_400 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::11] 11 3 final=Some (Gval (Fuint 1) (global_word_400 v)).
Proof.
 have Typed := types 400%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_400_step.
 - exact (prior 399%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_400 v sizes).
 - exact ran.
Qed.
Lemma global_progress_401 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;11] 3 final=Some (Gval (Fuint 1) (global_word_401 v)).
Proof.
 apply (global_sync_401_link invalid snapshot final v); [eapply global_progress_400; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_402 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;11] 24 final=Some (Gval (Fuint 1) (global_word_402 v)).
Proof.
 eapply global_node_402_step.
 - exact (prior 401%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_403 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;11] 26 final=Some (Gval (Fuint 1) (global_word_403 v)).
Proof.
 eapply global_node_403_step.
 - exact (prior 396%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact (prior 402%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_404 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(19 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;11] 28 final=Some (Gval (Fuint 1) (global_word_404 v)).
Proof.
 eapply global_node_404_step.
 - exact (prior 367%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact (prior 403%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_405 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;11] 27 final=Some (Gval (Fuint 1) (global_word_405 v)).
Proof.
 eapply global_node_405_step.
 - exact (prior 396%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact (prior 402%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_406 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(19 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;11] 29 final=Some (Gval (Fuint 1) (global_word_406 v)).
Proof.
 eapply global_node_406_step.
 - exact (prior 367%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact (prior 403%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_407 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(20 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;11] 30 final=Some (Gval (Fuint 1) (global_word_407 v)).
Proof.
 eapply global_node_407_step.
 - exact (prior 405%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact (prior 406%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (19 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_408 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(21 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;11] 31 final=Some (Gval (Fuint 2) (global_word_408 v)).
Proof.
 eapply global_node_408_step.
 - exact (prior 404%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (19 <= level)%coq_nat; lia))).
 - exact (prior 407%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (20 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_409 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(22 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;11] 32 final=Some (Gval (Fuint 2) (global_word_409 v)).
Proof.
 eapply global_node_409_step.
 - exact (prior 408%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (21 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_410 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(23 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;11] 33 final=Some (Gval (Fuint 1) (global_word_410 v)).
Proof.
 eapply global_node_410_step.
 - exact (prior 409%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (22 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_411.
Lemma global_connect_411_alias v : global_word_411 v = global_word_410 v.
Proof. unfold global_word_411, global_closed_411, global_expr_411, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_411.
Lemma global_progress_411 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(24 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;11] 5 final=Some (Gval (Fuint 1) (global_word_411 v)).
Proof.
 have Typed := types 411%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_411_step.
 - exact (prior 410%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (23 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_411_alias. apply adapt_uint_same. exact (global_size_410 v sizes).
 - exact ran.
Qed.
Lemma global_progress_412 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(25 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::11] 11 5 final=Some (Gval (Fuint 1) (global_word_412 v)).
Proof.
 apply (global_sync_412_link invalid snapshot final v); [eapply global_progress_411; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_413 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(26 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11] 41 final=Some (Gval (Fuint 1) (global_word_413 v)).
Proof.
 eapply global_node_413_step.
 - exact (prior 412%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (25 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_414.
Lemma global_connect_414_alias v : global_word_414 v = global_word_413 v.
Proof. unfold global_word_414, global_closed_414, global_expr_414, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_414.
Lemma global_progress_414 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(27 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11] 7 final=Some (Gval (Fuint 1) (global_word_414 v)).
Proof.
 have Typed := types 414%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_414_step.
 - exact (prior 413%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (26 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_414_alias. apply adapt_uint_same. exact (global_size_413 v sizes).
 - exact ran.
Qed.
Lemma global_progress_415 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(28 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 11 7 final=Some (Gval (Fuint 1) (global_word_415 v)).
Proof.
 apply (global_sync_415_link invalid snapshot final v); [eapply global_progress_414; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_416 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(29 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 313 final=Some (Gval (Fuint 1) (global_word_416 v)).
Proof.
 eapply global_node_416_step.
 - exact (prior 415%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (28 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_417 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(11 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;11] 34 final=Some (Gval (Fuint 1) (global_word_417 v)).
Proof.
 eapply global_node_417_step.
 - exact (prior 389%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (10 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_418.
Lemma global_connect_418_alias v : global_word_418 v = global_word_417 v.
Proof. unfold global_word_418, global_closed_418, global_expr_418, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_418.
Lemma global_progress_418 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(12 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;11] 6 final=Some (Gval (Fuint 1) (global_word_418 v)).
Proof.
 have Typed := types 418%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_418_step.
 - exact (prior 417%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (11 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_418_alias. apply adapt_uint_same. exact (global_size_417 v sizes).
 - exact ran.
Qed.
Lemma global_progress_419 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::11] 10 6 final=Some (Gval (Fuint 1) (global_word_419 v)).
Proof.
 apply (global_sync_419_link invalid snapshot final v); [eapply global_progress_418; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_420 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11] 42 final=Some (Gval (Fuint 1) (global_word_420 v)).
Proof.
 eapply global_node_420_step.
 - exact (prior 419%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_421.
Lemma global_connect_421_alias v : global_word_421 v = global_word_420 v.
Proof. unfold global_word_421, global_closed_421, global_expr_421, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_421.
Lemma global_progress_421 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11] 8 final=Some (Gval (Fuint 1) (global_word_421 v)).
Proof.
 have Typed := types 421%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_421_step.
 - exact (prior 420%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_421_alias. apply adapt_uint_same. exact (global_size_420 v sizes).
 - exact ran.
Qed.
Lemma global_progress_422 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 11 8 final=Some (Gval (Fuint 1) (global_word_422 v)).
Proof.
 apply (global_sync_422_link invalid snapshot final v); [eapply global_progress_421; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_423 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(17 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 314 final=Some (Gval (Fuint 1) (global_word_423 v)).
Proof.
 eapply global_node_423_step.
 - exact (prior 422%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_424 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(23 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;11] 34 final=Some (Gval (Fuint 1) (global_word_424 v)).
Proof.
 eapply global_node_424_step.
 - exact (prior 409%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (22 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_425.
Lemma global_connect_425_alias v : global_word_425 v = global_word_424 v.
Proof. unfold global_word_425, global_closed_425, global_expr_425, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_425.
Lemma global_progress_425 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(24 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;11] 6 final=Some (Gval (Fuint 1) (global_word_425 v)).
Proof.
 have Typed := types 425%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_425_step.
 - exact (prior 424%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (23 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_425_alias. apply adapt_uint_same. exact (global_size_424 v sizes).
 - exact ran.
Qed.
Lemma global_progress_426 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(25 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::11] 11 6 final=Some (Gval (Fuint 1) (global_word_426 v)).
Proof.
 apply (global_sync_426_link invalid snapshot final v); [eapply global_progress_425; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_427 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(26 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11] 43 final=Some (Gval (Fuint 1) (global_word_427 v)).
Proof.
 eapply global_node_427_step.
 - exact (prior 426%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (25 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_428.
Lemma global_connect_428_alias v : global_word_428 v = global_word_427 v.
Proof. unfold global_word_428, global_closed_428, global_expr_428, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_428.
Lemma global_progress_428 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(27 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11] 9 final=Some (Gval (Fuint 1) (global_word_428 v)).
Proof.
 have Typed := types 428%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_428_step.
 - exact (prior 427%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (26 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_428_alias. apply adapt_uint_same. exact (global_size_427 v sizes).
 - exact ran.
Qed.
Lemma global_progress_429 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(28 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 11 9 final=Some (Gval (Fuint 1) (global_word_429 v)).
Proof.
 apply (global_sync_429_link invalid snapshot final v); [eapply global_progress_428; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_430 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(29 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 315 final=Some (Gval (Fuint 1) (global_word_430 v)).
Proof.
 eapply global_node_430_step.
 - exact (prior 429%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (28 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_431 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 12 6 final=Some (Gval (Fuint 1) (global_word_431 v)).
Proof.
 have Typed := types 431%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_431_step.
 - exact (prior 423%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_431 v sizes).
 - exact ran.
Qed.
Lemma global_progress_432 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(19 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::12] 6 final=Some (Gval (Fuint 1) (global_word_432 v)).
Proof.
 apply (global_sync_432_link invalid snapshot final v); [eapply global_progress_431; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_433 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(20 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::12] 40 final=Some (Gval (Fuint 1) (global_word_433 v)).
Proof.
 eapply global_node_433_step.
 - exact (prior 432%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (19 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_434 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(21 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::12] 11 4 final=Some (Gval (Fuint 1) (global_word_434 v)).
Proof.
 have Typed := types 434%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_434_step.
 - exact (prior 433%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (20 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_434 v sizes).
 - exact ran.
Qed.
Lemma global_progress_435 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(22 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;12] 4 final=Some (Gval (Fuint 1) (global_word_435 v)).
Proof.
 apply (global_sync_435_link invalid snapshot final v); [eapply global_progress_434; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_436 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(23 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;12] 25 final=Some (Gval (Fuint 1) (global_word_436 v)).
Proof.
 eapply global_node_436_step.
 - exact (prior 435%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (22 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_437 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 12 4 final=Some (Gval (Fuint 1) (global_word_437 v)).
Proof.
 have Typed := types 437%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_437_step.
 - exact (prior 19%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_437 v sizes).
 - exact ran.
Qed.
Lemma global_progress_438 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::12] 4 final=Some (Gval (Fuint 1) (global_word_438 v)).
Proof.
 apply (global_sync_438_link invalid snapshot final v); [eapply global_progress_437; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_439 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::12] 10 4 final=Some (Gval (Fuint 1) (global_word_439 v)).
Proof.
 have Typed := types 439%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_439_step.
 - exact (prior 438%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_439 v sizes).
 - exact ran.
Qed.
Lemma global_progress_440 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;12] 4 final=Some (Gval (Fuint 1) (global_word_440 v)).
Proof.
 apply (global_sync_440_link invalid snapshot final v); [eapply global_progress_439; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_441 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;12] 25 final=Some (Gval (Fuint 1) (global_word_441 v)).
Proof.
 eapply global_node_441_step.
 - exact (prior 440%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_442 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 12 2 final=Some (Gval (Fuint 1) (global_word_442 v)).
Proof.
 have Typed := types 442%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_442_step.
 - exact (prior 17%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_442 v sizes).
 - exact ran.
Qed.
Lemma global_progress_443 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::12] 2 final=Some (Gval (Fuint 1) (global_word_443 v)).
Proof.
 apply (global_sync_443_link invalid snapshot final v); [eapply global_progress_442; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_444 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::12] 10 2 final=Some (Gval (Fuint 1) (global_word_444 v)).
Proof.
 have Typed := types 444%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_444_step.
 - exact (prior 443%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_444 v sizes).
 - exact ran.
Qed.
Lemma global_progress_445 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;12] 2 final=Some (Gval (Fuint 1) (global_word_445 v)).
Proof.
 apply (global_sync_445_link invalid snapshot final v); [eapply global_progress_444; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_446 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;12] 23 final=Some (Gval (Fuint 1) (global_word_446 v)).
Proof.
 eapply global_node_446_step.
 - exact (prior 445%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_447 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 12 3 final=Some (Gval (Fuint 1) (global_word_447 v)).
Proof.
 have Typed := types 447%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_447_step.
 - exact (prior 18%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_447 v sizes).
 - exact ran.
Qed.
Lemma global_progress_448 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::12] 3 final=Some (Gval (Fuint 1) (global_word_448 v)).
Proof.
 apply (global_sync_448_link invalid snapshot final v); [eapply global_progress_447; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_449 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::12] 10 3 final=Some (Gval (Fuint 1) (global_word_449 v)).
Proof.
 have Typed := types 449%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_449_step.
 - exact (prior 448%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_449 v sizes).
 - exact ran.
Qed.
Lemma global_progress_450 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;12] 3 final=Some (Gval (Fuint 1) (global_word_450 v)).
Proof.
 apply (global_sync_450_link invalid snapshot final v); [eapply global_progress_449; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_451 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;12] 24 final=Some (Gval (Fuint 1) (global_word_451 v)).
Proof.
 eapply global_node_451_step.
 - exact (prior 450%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_452 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;12] 26 final=Some (Gval (Fuint 1) (global_word_452 v)).
Proof.
 eapply global_node_452_step.
 - exact (prior 446%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 451%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_453 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(7 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;12] 28 final=Some (Gval (Fuint 1) (global_word_453 v)).
Proof.
 eapply global_node_453_step.
 - exact (prior 441%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 452%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_454 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;12] 27 final=Some (Gval (Fuint 1) (global_word_454 v)).
Proof.
 eapply global_node_454_step.
 - exact (prior 446%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 451%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_455 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(7 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;12] 29 final=Some (Gval (Fuint 1) (global_word_455 v)).
Proof.
 eapply global_node_455_step.
 - exact (prior 441%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 452%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_456 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(8 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;12] 30 final=Some (Gval (Fuint 1) (global_word_456 v)).
Proof.
 eapply global_node_456_step.
 - exact (prior 454%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact (prior 455%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (7 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_457 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(9 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;12] 31 final=Some (Gval (Fuint 2) (global_word_457 v)).
Proof.
 eapply global_node_457_step.
 - exact (prior 453%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (7 <= level)%coq_nat; lia))).
 - exact (prior 456%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (8 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_458 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(10 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;12] 32 final=Some (Gval (Fuint 2) (global_word_458 v)).
Proof.
 eapply global_node_458_step.
 - exact (prior 457%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (9 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_459 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(11 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;12] 33 final=Some (Gval (Fuint 1) (global_word_459 v)).
Proof.
 eapply global_node_459_step.
 - exact (prior 458%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (10 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_460.
Lemma global_connect_460_alias v : global_word_460 v = global_word_459 v.
Proof. unfold global_word_460, global_closed_460, global_expr_460, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_460.
Lemma global_progress_460 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(12 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;12] 5 final=Some (Gval (Fuint 1) (global_word_460 v)).
Proof.
 have Typed := types 460%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_460_step.
 - exact (prior 459%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (11 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_460_alias. apply adapt_uint_same. exact (global_size_459 v sizes).
 - exact ran.
Qed.
Lemma global_progress_461 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::12] 10 5 final=Some (Gval (Fuint 1) (global_word_461 v)).
Proof.
 apply (global_sync_461_link invalid snapshot final v); [eapply global_progress_460; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_462 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::12] 38 final=Some (Gval (Fuint 1) (global_word_462 v)).
Proof.
 eapply global_node_462_step.
 - exact (prior 461%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_463 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::12] 11 2 final=Some (Gval (Fuint 1) (global_word_463 v)).
Proof.
 have Typed := types 463%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_463_step.
 - exact (prior 462%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_463 v sizes).
 - exact ran.
Qed.
Lemma global_progress_464 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;12] 2 final=Some (Gval (Fuint 1) (global_word_464 v)).
Proof.
 apply (global_sync_464_link invalid snapshot final v); [eapply global_progress_463; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_465 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(17 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;12] 23 final=Some (Gval (Fuint 1) (global_word_465 v)).
Proof.
 eapply global_node_465_step.
 - exact (prior 464%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_466 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 12 5 final=Some (Gval (Fuint 1) (global_word_466 v)).
Proof.
 have Typed := types 466%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_466_step.
 - exact (prior 20%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_466 v sizes).
 - exact ran.
Qed.
Lemma global_progress_467 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::12] 5 final=Some (Gval (Fuint 1) (global_word_467 v)).
Proof.
 apply (global_sync_467_link invalid snapshot final v); [eapply global_progress_466; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_468 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::12] 39 final=Some (Gval (Fuint 1) (global_word_468 v)).
Proof.
 eapply global_node_468_step.
 - exact (prior 467%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_469 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::12] 11 3 final=Some (Gval (Fuint 1) (global_word_469 v)).
Proof.
 have Typed := types 469%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_469_step.
 - exact (prior 468%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_469 v sizes).
 - exact ran.
Qed.
Lemma global_progress_470 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;12] 3 final=Some (Gval (Fuint 1) (global_word_470 v)).
Proof.
 apply (global_sync_470_link invalid snapshot final v); [eapply global_progress_469; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_471 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;12] 24 final=Some (Gval (Fuint 1) (global_word_471 v)).
Proof.
 eapply global_node_471_step.
 - exact (prior 470%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_472 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;12] 26 final=Some (Gval (Fuint 1) (global_word_472 v)).
Proof.
 eapply global_node_472_step.
 - exact (prior 465%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact (prior 471%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_473 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(24 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;12] 28 final=Some (Gval (Fuint 1) (global_word_473 v)).
Proof.
 eapply global_node_473_step.
 - exact (prior 436%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (23 <= level)%coq_nat; lia))).
 - exact (prior 472%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_474 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;12] 27 final=Some (Gval (Fuint 1) (global_word_474 v)).
Proof.
 eapply global_node_474_step.
 - exact (prior 465%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact (prior 471%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_475 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(24 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;12] 29 final=Some (Gval (Fuint 1) (global_word_475 v)).
Proof.
 eapply global_node_475_step.
 - exact (prior 436%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (23 <= level)%coq_nat; lia))).
 - exact (prior 472%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_476 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(25 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;12] 30 final=Some (Gval (Fuint 1) (global_word_476 v)).
Proof.
 eapply global_node_476_step.
 - exact (prior 474%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact (prior 475%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (24 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_477 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(26 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;12] 31 final=Some (Gval (Fuint 2) (global_word_477 v)).
Proof.
 eapply global_node_477_step.
 - exact (prior 473%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (24 <= level)%coq_nat; lia))).
 - exact (prior 476%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (25 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_478 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(27 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;12] 32 final=Some (Gval (Fuint 2) (global_word_478 v)).
Proof.
 eapply global_node_478_step.
 - exact (prior 477%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (26 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_479 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(28 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;12] 33 final=Some (Gval (Fuint 1) (global_word_479 v)).
Proof.
 eapply global_node_479_step.
 - exact (prior 478%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (27 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_480.
Lemma global_connect_480_alias v : global_word_480 v = global_word_479 v.
Proof. unfold global_word_480, global_closed_480, global_expr_480, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_480.
Lemma global_progress_480 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(29 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;12] 5 final=Some (Gval (Fuint 1) (global_word_480 v)).
Proof.
 have Typed := types 480%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_480_step.
 - exact (prior 479%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (28 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_480_alias. apply adapt_uint_same. exact (global_size_479 v sizes).
 - exact ran.
Qed.
Lemma global_progress_481 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(30 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::12] 11 5 final=Some (Gval (Fuint 1) (global_word_481 v)).
Proof.
 apply (global_sync_481_link invalid snapshot final v); [eapply global_progress_480; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_482 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(31 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::12] 41 final=Some (Gval (Fuint 1) (global_word_482 v)).
Proof.
 eapply global_node_482_step.
 - exact (prior 481%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (30 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_483.
Lemma global_connect_483_alias v : global_word_483 v = global_word_482 v.
Proof. unfold global_word_483, global_closed_483, global_expr_483, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_483.
Lemma global_progress_483 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(32 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::12] 7 final=Some (Gval (Fuint 1) (global_word_483 v)).
Proof.
 have Typed := types 483%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_483_step.
 - exact (prior 482%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (31 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_483_alias. apply adapt_uint_same. exact (global_size_482 v sizes).
 - exact ran.
Qed.
Lemma global_progress_484 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(33 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 12 7 final=Some (Gval (Fuint 1) (global_word_484 v)).
Proof.
 apply (global_sync_484_link invalid snapshot final v); [eapply global_progress_483; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_485 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(34 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 316 final=Some (Gval (Fuint 1) (global_word_485 v)).
Proof.
 eapply global_node_485_step.
 - exact (prior 484%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (33 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_486 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(11 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;12] 34 final=Some (Gval (Fuint 1) (global_word_486 v)).
Proof.
 eapply global_node_486_step.
 - exact (prior 458%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (10 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_487.
Lemma global_connect_487_alias v : global_word_487 v = global_word_486 v.
Proof. unfold global_word_487, global_closed_487, global_expr_487, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_487.
Lemma global_progress_487 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(12 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;12] 6 final=Some (Gval (Fuint 1) (global_word_487 v)).
Proof.
 have Typed := types 487%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_487_step.
 - exact (prior 486%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (11 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_487_alias. apply adapt_uint_same. exact (global_size_486 v sizes).
 - exact ran.
Qed.
Lemma global_progress_488 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::12] 10 6 final=Some (Gval (Fuint 1) (global_word_488 v)).
Proof.
 apply (global_sync_488_link invalid snapshot final v); [eapply global_progress_487; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_489 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::12] 42 final=Some (Gval (Fuint 1) (global_word_489 v)).
Proof.
 eapply global_node_489_step.
 - exact (prior 488%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_490.
Lemma global_connect_490_alias v : global_word_490 v = global_word_489 v.
Proof. unfold global_word_490, global_closed_490, global_expr_490, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_490.
Lemma global_progress_490 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::12] 8 final=Some (Gval (Fuint 1) (global_word_490 v)).
Proof.
 have Typed := types 490%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_490_step.
 - exact (prior 489%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_490_alias. apply adapt_uint_same. exact (global_size_489 v sizes).
 - exact ran.
Qed.
Lemma global_progress_491 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 12 8 final=Some (Gval (Fuint 1) (global_word_491 v)).
Proof.
 apply (global_sync_491_link invalid snapshot final v); [eapply global_progress_490; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_492 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(17 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 317 final=Some (Gval (Fuint 1) (global_word_492 v)).
Proof.
 eapply global_node_492_step.
 - exact (prior 491%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_493 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(28 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;12] 34 final=Some (Gval (Fuint 1) (global_word_493 v)).
Proof.
 eapply global_node_493_step.
 - exact (prior 478%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (27 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_494.
Lemma global_connect_494_alias v : global_word_494 v = global_word_493 v.
Proof. unfold global_word_494, global_closed_494, global_expr_494, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_494.
Lemma global_progress_494 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(29 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;12] 6 final=Some (Gval (Fuint 1) (global_word_494 v)).
Proof.
 have Typed := types 494%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_494_step.
 - exact (prior 493%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (28 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_494_alias. apply adapt_uint_same. exact (global_size_493 v sizes).
 - exact ran.
Qed.
Lemma global_progress_495 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(30 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::12] 11 6 final=Some (Gval (Fuint 1) (global_word_495 v)).
Proof.
 apply (global_sync_495_link invalid snapshot final v); [eapply global_progress_494; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_496 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(31 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::12] 43 final=Some (Gval (Fuint 1) (global_word_496 v)).
Proof.
 eapply global_node_496_step.
 - exact (prior 495%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (30 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_497.
Lemma global_connect_497_alias v : global_word_497 v = global_word_496 v.
Proof. unfold global_word_497, global_closed_497, global_expr_497, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_497.
Lemma global_progress_497 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(32 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::12] 9 final=Some (Gval (Fuint 1) (global_word_497 v)).
Proof.
 have Typed := types 497%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_497_step.
 - exact (prior 496%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (31 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_497_alias. apply adapt_uint_same. exact (global_size_496 v sizes).
 - exact ran.
Qed.
Lemma global_progress_498 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(33 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 12 9 final=Some (Gval (Fuint 1) (global_word_498 v)).
Proof.
 apply (global_sync_498_link invalid snapshot final v); [eapply global_progress_497; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_499 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(34 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 318 final=Some (Gval (Fuint 1) (global_word_499 v)).
Proof.
 eapply global_node_499_step.
 - exact (prior 498%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (33 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_500 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 13 6 final=Some (Gval (Fuint 1) (global_word_500 v)).
Proof.
 have Typed := types 500%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_500_step.
 - exact (prior 492%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_500 v sizes).
 - exact ran.
Qed.
Lemma global_progress_501 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(19 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::13] 6 final=Some (Gval (Fuint 1) (global_word_501 v)).
Proof.
 apply (global_sync_501_link invalid snapshot final v); [eapply global_progress_500; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_502 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(20 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::13] 40 final=Some (Gval (Fuint 1) (global_word_502 v)).
Proof.
 eapply global_node_502_step.
 - exact (prior 501%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (19 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_503 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(21 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::13] 11 4 final=Some (Gval (Fuint 1) (global_word_503 v)).
Proof.
 have Typed := types 503%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_503_step.
 - exact (prior 502%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (20 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_503 v sizes).
 - exact ran.
Qed.
Lemma global_progress_504 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(22 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;13] 4 final=Some (Gval (Fuint 1) (global_word_504 v)).
Proof.
 apply (global_sync_504_link invalid snapshot final v); [eapply global_progress_503; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_505 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(23 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;13] 25 final=Some (Gval (Fuint 1) (global_word_505 v)).
Proof.
 eapply global_node_505_step.
 - exact (prior 504%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (22 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_506 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 13 4 final=Some (Gval (Fuint 1) (global_word_506 v)).
Proof.
 have Typed := types 506%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_506_step.
 - exact (prior 23%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_506 v sizes).
 - exact ran.
Qed.
Lemma global_progress_507 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::13] 4 final=Some (Gval (Fuint 1) (global_word_507 v)).
Proof.
 apply (global_sync_507_link invalid snapshot final v); [eapply global_progress_506; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_508 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::13] 10 4 final=Some (Gval (Fuint 1) (global_word_508 v)).
Proof.
 have Typed := types 508%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_508_step.
 - exact (prior 507%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_508 v sizes).
 - exact ran.
Qed.
Lemma global_progress_509 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;13] 4 final=Some (Gval (Fuint 1) (global_word_509 v)).
Proof.
 apply (global_sync_509_link invalid snapshot final v); [eapply global_progress_508; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_510 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;13] 25 final=Some (Gval (Fuint 1) (global_word_510 v)).
Proof.
 eapply global_node_510_step.
 - exact (prior 509%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_511 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 13 2 final=Some (Gval (Fuint 1) (global_word_511 v)).
Proof.
 have Typed := types 511%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_511_step.
 - exact (prior 21%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_511 v sizes).
 - exact ran.
Qed.
Lemma global_progress_512 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::13] 2 final=Some (Gval (Fuint 1) (global_word_512 v)).
Proof.
 apply (global_sync_512_link invalid snapshot final v); [eapply global_progress_511; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_513 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::13] 10 2 final=Some (Gval (Fuint 1) (global_word_513 v)).
Proof.
 have Typed := types 513%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_513_step.
 - exact (prior 512%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_513 v sizes).
 - exact ran.
Qed.
Lemma global_progress_514 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;13] 2 final=Some (Gval (Fuint 1) (global_word_514 v)).
Proof.
 apply (global_sync_514_link invalid snapshot final v); [eapply global_progress_513; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_515 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;13] 23 final=Some (Gval (Fuint 1) (global_word_515 v)).
Proof.
 eapply global_node_515_step.
 - exact (prior 514%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_516 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 13 3 final=Some (Gval (Fuint 1) (global_word_516 v)).
Proof.
 have Typed := types 516%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_516_step.
 - exact (prior 22%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_516 v sizes).
 - exact ran.
Qed.
Lemma global_progress_517 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::13] 3 final=Some (Gval (Fuint 1) (global_word_517 v)).
Proof.
 apply (global_sync_517_link invalid snapshot final v); [eapply global_progress_516; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_518 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::13] 10 3 final=Some (Gval (Fuint 1) (global_word_518 v)).
Proof.
 have Typed := types 518%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_518_step.
 - exact (prior 517%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_518 v sizes).
 - exact ran.
Qed.
Lemma global_progress_519 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;13] 3 final=Some (Gval (Fuint 1) (global_word_519 v)).
Proof.
 apply (global_sync_519_link invalid snapshot final v); [eapply global_progress_518; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_520 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;13] 24 final=Some (Gval (Fuint 1) (global_word_520 v)).
Proof.
 eapply global_node_520_step.
 - exact (prior 519%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_521 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;13] 26 final=Some (Gval (Fuint 1) (global_word_521 v)).
Proof.
 eapply global_node_521_step.
 - exact (prior 515%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 520%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_522 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(7 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;13] 28 final=Some (Gval (Fuint 1) (global_word_522 v)).
Proof.
 eapply global_node_522_step.
 - exact (prior 510%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 521%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_523 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;13] 27 final=Some (Gval (Fuint 1) (global_word_523 v)).
Proof.
 eapply global_node_523_step.
 - exact (prior 515%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 520%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_524 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(7 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;13] 29 final=Some (Gval (Fuint 1) (global_word_524 v)).
Proof.
 eapply global_node_524_step.
 - exact (prior 510%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 521%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_525 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(8 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;13] 30 final=Some (Gval (Fuint 1) (global_word_525 v)).
Proof.
 eapply global_node_525_step.
 - exact (prior 523%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact (prior 524%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (7 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_526 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(9 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;13] 31 final=Some (Gval (Fuint 2) (global_word_526 v)).
Proof.
 eapply global_node_526_step.
 - exact (prior 522%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (7 <= level)%coq_nat; lia))).
 - exact (prior 525%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (8 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_527 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(10 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;13] 32 final=Some (Gval (Fuint 2) (global_word_527 v)).
Proof.
 eapply global_node_527_step.
 - exact (prior 526%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (9 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_528 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(11 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;13] 33 final=Some (Gval (Fuint 1) (global_word_528 v)).
Proof.
 eapply global_node_528_step.
 - exact (prior 527%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (10 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_529.
Lemma global_connect_529_alias v : global_word_529 v = global_word_528 v.
Proof. unfold global_word_529, global_closed_529, global_expr_529, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_529.
Lemma global_progress_529 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(12 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;13] 5 final=Some (Gval (Fuint 1) (global_word_529 v)).
Proof.
 have Typed := types 529%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_529_step.
 - exact (prior 528%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (11 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_529_alias. apply adapt_uint_same. exact (global_size_528 v sizes).
 - exact ran.
Qed.
Lemma global_progress_530 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::13] 10 5 final=Some (Gval (Fuint 1) (global_word_530 v)).
Proof.
 apply (global_sync_530_link invalid snapshot final v); [eapply global_progress_529; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_531 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::13] 38 final=Some (Gval (Fuint 1) (global_word_531 v)).
Proof.
 eapply global_node_531_step.
 - exact (prior 530%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_532 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::13] 11 2 final=Some (Gval (Fuint 1) (global_word_532 v)).
Proof.
 have Typed := types 532%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_532_step.
 - exact (prior 531%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_532 v sizes).
 - exact ran.
Qed.
Lemma global_progress_533 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;13] 2 final=Some (Gval (Fuint 1) (global_word_533 v)).
Proof.
 apply (global_sync_533_link invalid snapshot final v); [eapply global_progress_532; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_534 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(17 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;13] 23 final=Some (Gval (Fuint 1) (global_word_534 v)).
Proof.
 eapply global_node_534_step.
 - exact (prior 533%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_535 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 13 5 final=Some (Gval (Fuint 1) (global_word_535 v)).
Proof.
 have Typed := types 535%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_535_step.
 - exact (prior 24%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_535 v sizes).
 - exact ran.
Qed.
Lemma global_progress_536 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::13] 5 final=Some (Gval (Fuint 1) (global_word_536 v)).
Proof.
 apply (global_sync_536_link invalid snapshot final v); [eapply global_progress_535; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_537 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::13] 39 final=Some (Gval (Fuint 1) (global_word_537 v)).
Proof.
 eapply global_node_537_step.
 - exact (prior 536%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_538 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::13] 11 3 final=Some (Gval (Fuint 1) (global_word_538 v)).
Proof.
 have Typed := types 538%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_538_step.
 - exact (prior 537%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_538 v sizes).
 - exact ran.
Qed.
Lemma global_progress_539 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;13] 3 final=Some (Gval (Fuint 1) (global_word_539 v)).
Proof.
 apply (global_sync_539_link invalid snapshot final v); [eapply global_progress_538; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_540 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;13] 24 final=Some (Gval (Fuint 1) (global_word_540 v)).
Proof.
 eapply global_node_540_step.
 - exact (prior 539%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_541 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;13] 26 final=Some (Gval (Fuint 1) (global_word_541 v)).
Proof.
 eapply global_node_541_step.
 - exact (prior 534%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact (prior 540%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_542 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(24 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;13] 28 final=Some (Gval (Fuint 1) (global_word_542 v)).
Proof.
 eapply global_node_542_step.
 - exact (prior 505%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (23 <= level)%coq_nat; lia))).
 - exact (prior 541%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_543 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;13] 27 final=Some (Gval (Fuint 1) (global_word_543 v)).
Proof.
 eapply global_node_543_step.
 - exact (prior 534%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact (prior 540%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_544 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(24 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;13] 29 final=Some (Gval (Fuint 1) (global_word_544 v)).
Proof.
 eapply global_node_544_step.
 - exact (prior 505%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (23 <= level)%coq_nat; lia))).
 - exact (prior 541%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_545 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(25 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;13] 30 final=Some (Gval (Fuint 1) (global_word_545 v)).
Proof.
 eapply global_node_545_step.
 - exact (prior 543%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact (prior 544%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (24 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_546 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(26 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;13] 31 final=Some (Gval (Fuint 2) (global_word_546 v)).
Proof.
 eapply global_node_546_step.
 - exact (prior 542%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (24 <= level)%coq_nat; lia))).
 - exact (prior 545%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (25 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_547 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(27 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;13] 32 final=Some (Gval (Fuint 2) (global_word_547 v)).
Proof.
 eapply global_node_547_step.
 - exact (prior 546%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (26 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_548 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(28 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;13] 33 final=Some (Gval (Fuint 1) (global_word_548 v)).
Proof.
 eapply global_node_548_step.
 - exact (prior 547%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (27 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_549.
Lemma global_connect_549_alias v : global_word_549 v = global_word_548 v.
Proof. unfold global_word_549, global_closed_549, global_expr_549, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_549.
Lemma global_progress_549 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(29 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;13] 5 final=Some (Gval (Fuint 1) (global_word_549 v)).
Proof.
 have Typed := types 549%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_549_step.
 - exact (prior 548%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (28 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_549_alias. apply adapt_uint_same. exact (global_size_548 v sizes).
 - exact ran.
Qed.
Lemma global_progress_550 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(30 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::13] 11 5 final=Some (Gval (Fuint 1) (global_word_550 v)).
Proof.
 apply (global_sync_550_link invalid snapshot final v); [eapply global_progress_549; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_551 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(31 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::13] 41 final=Some (Gval (Fuint 1) (global_word_551 v)).
Proof.
 eapply global_node_551_step.
 - exact (prior 550%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (30 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_552.
Lemma global_connect_552_alias v : global_word_552 v = global_word_551 v.
Proof. unfold global_word_552, global_closed_552, global_expr_552, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_552.
Lemma global_progress_552 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(32 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::13] 7 final=Some (Gval (Fuint 1) (global_word_552 v)).
Proof.
 have Typed := types 552%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_552_step.
 - exact (prior 551%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (31 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_552_alias. apply adapt_uint_same. exact (global_size_551 v sizes).
 - exact ran.
Qed.
Lemma global_progress_553 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(33 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 13 7 final=Some (Gval (Fuint 1) (global_word_553 v)).
Proof.
 apply (global_sync_553_link invalid snapshot final v); [eapply global_progress_552; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_554 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(34 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 319 final=Some (Gval (Fuint 1) (global_word_554 v)).
Proof.
 eapply global_node_554_step.
 - exact (prior 553%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (33 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_555 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(11 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;13] 34 final=Some (Gval (Fuint 1) (global_word_555 v)).
Proof.
 eapply global_node_555_step.
 - exact (prior 527%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (10 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_556.
Lemma global_connect_556_alias v : global_word_556 v = global_word_555 v.
Proof. unfold global_word_556, global_closed_556, global_expr_556, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_556.
Lemma global_progress_556 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(12 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;13] 6 final=Some (Gval (Fuint 1) (global_word_556 v)).
Proof.
 have Typed := types 556%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_556_step.
 - exact (prior 555%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (11 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_556_alias. apply adapt_uint_same. exact (global_size_555 v sizes).
 - exact ran.
Qed.
Lemma global_progress_557 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::13] 10 6 final=Some (Gval (Fuint 1) (global_word_557 v)).
Proof.
 apply (global_sync_557_link invalid snapshot final v); [eapply global_progress_556; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_558 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::13] 42 final=Some (Gval (Fuint 1) (global_word_558 v)).
Proof.
 eapply global_node_558_step.
 - exact (prior 557%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_559.
Lemma global_connect_559_alias v : global_word_559 v = global_word_558 v.
Proof. unfold global_word_559, global_closed_559, global_expr_559, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_559.
Lemma global_progress_559 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::13] 8 final=Some (Gval (Fuint 1) (global_word_559 v)).
Proof.
 have Typed := types 559%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_559_step.
 - exact (prior 558%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_559_alias. apply adapt_uint_same. exact (global_size_558 v sizes).
 - exact ran.
Qed.
Lemma global_progress_560 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 13 8 final=Some (Gval (Fuint 1) (global_word_560 v)).
Proof.
 apply (global_sync_560_link invalid snapshot final v); [eapply global_progress_559; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_561 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(17 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 320 final=Some (Gval (Fuint 1) (global_word_561 v)).
Proof.
 eapply global_node_561_step.
 - exact (prior 560%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_562 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(28 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;13] 34 final=Some (Gval (Fuint 1) (global_word_562 v)).
Proof.
 eapply global_node_562_step.
 - exact (prior 547%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (27 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_563.
Lemma global_connect_563_alias v : global_word_563 v = global_word_562 v.
Proof. unfold global_word_563, global_closed_563, global_expr_563, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_563.
Lemma global_progress_563 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(29 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;13] 6 final=Some (Gval (Fuint 1) (global_word_563 v)).
Proof.
 have Typed := types 563%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_563_step.
 - exact (prior 562%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (28 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_563_alias. apply adapt_uint_same. exact (global_size_562 v sizes).
 - exact ran.
Qed.
Lemma global_progress_564 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(30 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::13] 11 6 final=Some (Gval (Fuint 1) (global_word_564 v)).
Proof.
 apply (global_sync_564_link invalid snapshot final v); [eapply global_progress_563; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_565 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(31 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::13] 43 final=Some (Gval (Fuint 1) (global_word_565 v)).
Proof.
 eapply global_node_565_step.
 - exact (prior 564%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (30 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_566.
Lemma global_connect_566_alias v : global_word_566 v = global_word_565 v.
Proof. unfold global_word_566, global_closed_566, global_expr_566, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_566.
Lemma global_progress_566 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(32 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::13] 9 final=Some (Gval (Fuint 1) (global_word_566 v)).
Proof.
 have Typed := types 566%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_566_step.
 - exact (prior 565%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (31 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_566_alias. apply adapt_uint_same. exact (global_size_565 v sizes).
 - exact ran.
Qed.
Lemma global_progress_567 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(33 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 13 9 final=Some (Gval (Fuint 1) (global_word_567 v)).
Proof.
 apply (global_sync_567_link invalid snapshot final v); [eapply global_progress_566; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_568 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(34 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 321 final=Some (Gval (Fuint 1) (global_word_568 v)).
Proof.
 eapply global_node_568_step.
 - exact (prior 567%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (33 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_569 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 14 6 final=Some (Gval (Fuint 1) (global_word_569 v)).
Proof.
 have Typed := types 569%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_569_step.
 - exact (prior 561%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_569 v sizes).
 - exact ran.
Qed.
Lemma global_progress_570 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(19 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::14] 6 final=Some (Gval (Fuint 1) (global_word_570 v)).
Proof.
 apply (global_sync_570_link invalid snapshot final v); [eapply global_progress_569; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_571 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(20 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::14] 40 final=Some (Gval (Fuint 1) (global_word_571 v)).
Proof.
 eapply global_node_571_step.
 - exact (prior 570%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (19 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_572 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(21 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::14] 11 4 final=Some (Gval (Fuint 1) (global_word_572 v)).
Proof.
 have Typed := types 572%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_572_step.
 - exact (prior 571%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (20 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_572 v sizes).
 - exact ran.
Qed.
Lemma global_progress_573 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(22 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;14] 4 final=Some (Gval (Fuint 1) (global_word_573 v)).
Proof.
 apply (global_sync_573_link invalid snapshot final v); [eapply global_progress_572; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_574 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(23 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;14] 25 final=Some (Gval (Fuint 1) (global_word_574 v)).
Proof.
 eapply global_node_574_step.
 - exact (prior 573%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (22 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_575 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 14 4 final=Some (Gval (Fuint 1) (global_word_575 v)).
Proof.
 have Typed := types 575%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_575_step.
 - exact (prior 28%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_575 v sizes).
 - exact ran.
Qed.
Lemma global_progress_576 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::14] 4 final=Some (Gval (Fuint 1) (global_word_576 v)).
Proof.
 apply (global_sync_576_link invalid snapshot final v); [eapply global_progress_575; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_577 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::14] 10 4 final=Some (Gval (Fuint 1) (global_word_577 v)).
Proof.
 have Typed := types 577%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_577_step.
 - exact (prior 576%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_577 v sizes).
 - exact ran.
Qed.
Lemma global_progress_578 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;14] 4 final=Some (Gval (Fuint 1) (global_word_578 v)).
Proof.
 apply (global_sync_578_link invalid snapshot final v); [eapply global_progress_577; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_579 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;14] 25 final=Some (Gval (Fuint 1) (global_word_579 v)).
Proof.
 eapply global_node_579_step.
 - exact (prior 578%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_580 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 14 2 final=Some (Gval (Fuint 1) (global_word_580 v)).
Proof.
 have Typed := types 580%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_580_step.
 - exact (prior 26%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_580 v sizes).
 - exact ran.
Qed.
Lemma global_progress_581 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::14] 2 final=Some (Gval (Fuint 1) (global_word_581 v)).
Proof.
 apply (global_sync_581_link invalid snapshot final v); [eapply global_progress_580; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_582 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::14] 10 2 final=Some (Gval (Fuint 1) (global_word_582 v)).
Proof.
 have Typed := types 582%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_582_step.
 - exact (prior 581%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_582 v sizes).
 - exact ran.
Qed.
Lemma global_progress_583 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;14] 2 final=Some (Gval (Fuint 1) (global_word_583 v)).
Proof.
 apply (global_sync_583_link invalid snapshot final v); [eapply global_progress_582; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_584 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;14] 23 final=Some (Gval (Fuint 1) (global_word_584 v)).
Proof.
 eapply global_node_584_step.
 - exact (prior 583%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_585 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 14 3 final=Some (Gval (Fuint 1) (global_word_585 v)).
Proof.
 have Typed := types 585%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_585_step.
 - exact (prior 27%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_585 v sizes).
 - exact ran.
Qed.
Lemma global_progress_586 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::14] 3 final=Some (Gval (Fuint 1) (global_word_586 v)).
Proof.
 apply (global_sync_586_link invalid snapshot final v); [eapply global_progress_585; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_587 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::14] 10 3 final=Some (Gval (Fuint 1) (global_word_587 v)).
Proof.
 have Typed := types 587%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_587_step.
 - exact (prior 586%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_587 v sizes).
 - exact ran.
Qed.
Lemma global_progress_588 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;14] 3 final=Some (Gval (Fuint 1) (global_word_588 v)).
Proof.
 apply (global_sync_588_link invalid snapshot final v); [eapply global_progress_587; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_589 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;14] 24 final=Some (Gval (Fuint 1) (global_word_589 v)).
Proof.
 eapply global_node_589_step.
 - exact (prior 588%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_590 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;14] 26 final=Some (Gval (Fuint 1) (global_word_590 v)).
Proof.
 eapply global_node_590_step.
 - exact (prior 584%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 589%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_591 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(7 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;14] 28 final=Some (Gval (Fuint 1) (global_word_591 v)).
Proof.
 eapply global_node_591_step.
 - exact (prior 579%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 590%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_592 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;14] 27 final=Some (Gval (Fuint 1) (global_word_592 v)).
Proof.
 eapply global_node_592_step.
 - exact (prior 584%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 589%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_593 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(7 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;14] 29 final=Some (Gval (Fuint 1) (global_word_593 v)).
Proof.
 eapply global_node_593_step.
 - exact (prior 579%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 590%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_594 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(8 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;14] 30 final=Some (Gval (Fuint 1) (global_word_594 v)).
Proof.
 eapply global_node_594_step.
 - exact (prior 592%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact (prior 593%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (7 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_595 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(9 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;14] 31 final=Some (Gval (Fuint 2) (global_word_595 v)).
Proof.
 eapply global_node_595_step.
 - exact (prior 591%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (7 <= level)%coq_nat; lia))).
 - exact (prior 594%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (8 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_596 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(10 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;14] 32 final=Some (Gval (Fuint 2) (global_word_596 v)).
Proof.
 eapply global_node_596_step.
 - exact (prior 595%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (9 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_597 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(11 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;14] 33 final=Some (Gval (Fuint 1) (global_word_597 v)).
Proof.
 eapply global_node_597_step.
 - exact (prior 596%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (10 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_598.
Lemma global_connect_598_alias v : global_word_598 v = global_word_597 v.
Proof. unfold global_word_598, global_closed_598, global_expr_598, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_598.
Lemma global_progress_598 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(12 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;14] 5 final=Some (Gval (Fuint 1) (global_word_598 v)).
Proof.
 have Typed := types 598%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_598_step.
 - exact (prior 597%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (11 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_598_alias. apply adapt_uint_same. exact (global_size_597 v sizes).
 - exact ran.
Qed.
Lemma global_progress_599 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::14] 10 5 final=Some (Gval (Fuint 1) (global_word_599 v)).
Proof.
 apply (global_sync_599_link invalid snapshot final v); [eapply global_progress_598; try eassumption; lia|exact ran].
Qed.
