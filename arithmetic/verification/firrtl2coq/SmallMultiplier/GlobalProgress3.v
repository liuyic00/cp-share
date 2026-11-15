From Coq Require Import NArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import HierarchyFacts PortFieldFacts.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalWidthFacts GlobalNodeSteps GlobalFieldSteps GlobalScalarSteps GlobalSyncSteps GlobalLeaves.
Local Open Scope N_scope.
From SmallMultiplier Require Import GlobalProgressTypes.
From SmallMultiplier Require Export GlobalProgress2.
Lemma global_progress_600 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::14] 38 final=Some (Gval (Fuint 1) (global_word_600 v)).
Proof.
 eapply global_node_600_step.
 - exact (prior 599%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_601 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::14] 11 2 final=Some (Gval (Fuint 1) (global_word_601 v)).
Proof.
 have Typed := types 601%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_601_step.
 - exact (prior 600%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_601 v sizes).
 - exact ran.
Qed.
Lemma global_progress_602 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;14] 2 final=Some (Gval (Fuint 1) (global_word_602 v)).
Proof.
 apply (global_sync_602_link invalid snapshot final v); [eapply global_progress_601; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_603 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(17 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;14] 23 final=Some (Gval (Fuint 1) (global_word_603 v)).
Proof.
 eapply global_node_603_step.
 - exact (prior 602%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_604 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 14 5 final=Some (Gval (Fuint 1) (global_word_604 v)).
Proof.
 have Typed := types 604%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_604_step.
 - exact (prior 29%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_604 v sizes).
 - exact ran.
Qed.
Lemma global_progress_605 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::14] 5 final=Some (Gval (Fuint 1) (global_word_605 v)).
Proof.
 apply (global_sync_605_link invalid snapshot final v); [eapply global_progress_604; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_606 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::14] 39 final=Some (Gval (Fuint 1) (global_word_606 v)).
Proof.
 eapply global_node_606_step.
 - exact (prior 605%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_607 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::14] 11 3 final=Some (Gval (Fuint 1) (global_word_607 v)).
Proof.
 have Typed := types 607%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_607_step.
 - exact (prior 606%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_607 v sizes).
 - exact ran.
Qed.
Lemma global_progress_608 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;14] 3 final=Some (Gval (Fuint 1) (global_word_608 v)).
Proof.
 apply (global_sync_608_link invalid snapshot final v); [eapply global_progress_607; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_609 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;14] 24 final=Some (Gval (Fuint 1) (global_word_609 v)).
Proof.
 eapply global_node_609_step.
 - exact (prior 608%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_610 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;14] 26 final=Some (Gval (Fuint 1) (global_word_610 v)).
Proof.
 eapply global_node_610_step.
 - exact (prior 603%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact (prior 609%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_611 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(24 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;14] 28 final=Some (Gval (Fuint 1) (global_word_611 v)).
Proof.
 eapply global_node_611_step.
 - exact (prior 574%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (23 <= level)%coq_nat; lia))).
 - exact (prior 610%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_612 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;14] 27 final=Some (Gval (Fuint 1) (global_word_612 v)).
Proof.
 eapply global_node_612_step.
 - exact (prior 603%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact (prior 609%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_613 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(24 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;14] 29 final=Some (Gval (Fuint 1) (global_word_613 v)).
Proof.
 eapply global_node_613_step.
 - exact (prior 574%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (23 <= level)%coq_nat; lia))).
 - exact (prior 610%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_614 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(25 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;14] 30 final=Some (Gval (Fuint 1) (global_word_614 v)).
Proof.
 eapply global_node_614_step.
 - exact (prior 612%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact (prior 613%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (24 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_615 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(26 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;14] 31 final=Some (Gval (Fuint 2) (global_word_615 v)).
Proof.
 eapply global_node_615_step.
 - exact (prior 611%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (24 <= level)%coq_nat; lia))).
 - exact (prior 614%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (25 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_616 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(27 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;14] 32 final=Some (Gval (Fuint 2) (global_word_616 v)).
Proof.
 eapply global_node_616_step.
 - exact (prior 615%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (26 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_617 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(28 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;14] 33 final=Some (Gval (Fuint 1) (global_word_617 v)).
Proof.
 eapply global_node_617_step.
 - exact (prior 616%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (27 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_618.
Lemma global_connect_618_alias v : global_word_618 v = global_word_617 v.
Proof. unfold global_word_618, global_closed_618, global_expr_618, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_618.
Lemma global_progress_618 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(29 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;14] 5 final=Some (Gval (Fuint 1) (global_word_618 v)).
Proof.
 have Typed := types 618%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_618_step.
 - exact (prior 617%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (28 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_618_alias. apply adapt_uint_same. exact (global_size_617 v sizes).
 - exact ran.
Qed.
Lemma global_progress_619 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(30 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::14] 11 5 final=Some (Gval (Fuint 1) (global_word_619 v)).
Proof.
 apply (global_sync_619_link invalid snapshot final v); [eapply global_progress_618; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_620 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(31 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::14] 41 final=Some (Gval (Fuint 1) (global_word_620 v)).
Proof.
 eapply global_node_620_step.
 - exact (prior 619%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (30 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_621.
Lemma global_connect_621_alias v : global_word_621 v = global_word_620 v.
Proof. unfold global_word_621, global_closed_621, global_expr_621, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_621.
Lemma global_progress_621 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(32 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::14] 7 final=Some (Gval (Fuint 1) (global_word_621 v)).
Proof.
 have Typed := types 621%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_621_step.
 - exact (prior 620%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (31 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_621_alias. apply adapt_uint_same. exact (global_size_620 v sizes).
 - exact ran.
Qed.
Lemma global_progress_622 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(33 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 14 7 final=Some (Gval (Fuint 1) (global_word_622 v)).
Proof.
 apply (global_sync_622_link invalid snapshot final v); [eapply global_progress_621; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_623 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(34 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 322 final=Some (Gval (Fuint 1) (global_word_623 v)).
Proof.
 eapply global_node_623_step.
 - exact (prior 622%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (33 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_624 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(11 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;14] 34 final=Some (Gval (Fuint 1) (global_word_624 v)).
Proof.
 eapply global_node_624_step.
 - exact (prior 596%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (10 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_625.
Lemma global_connect_625_alias v : global_word_625 v = global_word_624 v.
Proof. unfold global_word_625, global_closed_625, global_expr_625, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_625.
Lemma global_progress_625 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(12 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;14] 6 final=Some (Gval (Fuint 1) (global_word_625 v)).
Proof.
 have Typed := types 625%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_625_step.
 - exact (prior 624%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (11 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_625_alias. apply adapt_uint_same. exact (global_size_624 v sizes).
 - exact ran.
Qed.
Lemma global_progress_626 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::14] 10 6 final=Some (Gval (Fuint 1) (global_word_626 v)).
Proof.
 apply (global_sync_626_link invalid snapshot final v); [eapply global_progress_625; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_627 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::14] 42 final=Some (Gval (Fuint 1) (global_word_627 v)).
Proof.
 eapply global_node_627_step.
 - exact (prior 626%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_628.
Lemma global_connect_628_alias v : global_word_628 v = global_word_627 v.
Proof. unfold global_word_628, global_closed_628, global_expr_628, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_628.
Lemma global_progress_628 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::14] 8 final=Some (Gval (Fuint 1) (global_word_628 v)).
Proof.
 have Typed := types 628%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_628_step.
 - exact (prior 627%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_628_alias. apply adapt_uint_same. exact (global_size_627 v sizes).
 - exact ran.
Qed.
Lemma global_progress_629 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 14 8 final=Some (Gval (Fuint 1) (global_word_629 v)).
Proof.
 apply (global_sync_629_link invalid snapshot final v); [eapply global_progress_628; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_630 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(17 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 323 final=Some (Gval (Fuint 1) (global_word_630 v)).
Proof.
 eapply global_node_630_step.
 - exact (prior 629%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_631 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(28 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;14] 34 final=Some (Gval (Fuint 1) (global_word_631 v)).
Proof.
 eapply global_node_631_step.
 - exact (prior 616%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (27 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_632.
Lemma global_connect_632_alias v : global_word_632 v = global_word_631 v.
Proof. unfold global_word_632, global_closed_632, global_expr_632, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_632.
Lemma global_progress_632 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(29 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;14] 6 final=Some (Gval (Fuint 1) (global_word_632 v)).
Proof.
 have Typed := types 632%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_632_step.
 - exact (prior 631%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (28 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_632_alias. apply adapt_uint_same. exact (global_size_631 v sizes).
 - exact ran.
Qed.
Lemma global_progress_633 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(30 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::14] 11 6 final=Some (Gval (Fuint 1) (global_word_633 v)).
Proof.
 apply (global_sync_633_link invalid snapshot final v); [eapply global_progress_632; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_634 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(31 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::14] 43 final=Some (Gval (Fuint 1) (global_word_634 v)).
Proof.
 eapply global_node_634_step.
 - exact (prior 633%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (30 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_635.
Lemma global_connect_635_alias v : global_word_635 v = global_word_634 v.
Proof. unfold global_word_635, global_closed_635, global_expr_635, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_635.
Lemma global_progress_635 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(32 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::14] 9 final=Some (Gval (Fuint 1) (global_word_635 v)).
Proof.
 have Typed := types 635%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_635_step.
 - exact (prior 634%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (31 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_635_alias. apply adapt_uint_same. exact (global_size_634 v sizes).
 - exact ran.
Qed.
Lemma global_progress_636 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(33 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 14 9 final=Some (Gval (Fuint 1) (global_word_636 v)).
Proof.
 apply (global_sync_636_link invalid snapshot final v); [eapply global_progress_635; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_637 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(34 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 324 final=Some (Gval (Fuint 1) (global_word_637 v)).
Proof.
 eapply global_node_637_step.
 - exact (prior 636%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (33 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_638 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 15 6 final=Some (Gval (Fuint 1) (global_word_638 v)).
Proof.
 have Typed := types 638%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_638_step.
 - exact (prior 630%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_638 v sizes).
 - exact ran.
Qed.
Lemma global_progress_639 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(19 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::15] 6 final=Some (Gval (Fuint 1) (global_word_639 v)).
Proof.
 apply (global_sync_639_link invalid snapshot final v); [eapply global_progress_638; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_640 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(20 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::15] 40 final=Some (Gval (Fuint 1) (global_word_640 v)).
Proof.
 eapply global_node_640_step.
 - exact (prior 639%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (19 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_641 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(21 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::15] 11 4 final=Some (Gval (Fuint 1) (global_word_641 v)).
Proof.
 have Typed := types 641%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_641_step.
 - exact (prior 640%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (20 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_641 v sizes).
 - exact ran.
Qed.
Lemma global_progress_642 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(22 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;15] 4 final=Some (Gval (Fuint 1) (global_word_642 v)).
Proof.
 apply (global_sync_642_link invalid snapshot final v); [eapply global_progress_641; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_643 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(23 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;15] 25 final=Some (Gval (Fuint 1) (global_word_643 v)).
Proof.
 eapply global_node_643_step.
 - exact (prior 642%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (22 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_644 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 15 4 final=Some (Gval (Fuint 1) (global_word_644 v)).
Proof.
 have Typed := types 644%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_644_step.
 - exact (prior 33%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_644 v sizes).
 - exact ran.
Qed.
Lemma global_progress_645 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::15] 4 final=Some (Gval (Fuint 1) (global_word_645 v)).
Proof.
 apply (global_sync_645_link invalid snapshot final v); [eapply global_progress_644; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_646 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::15] 10 4 final=Some (Gval (Fuint 1) (global_word_646 v)).
Proof.
 have Typed := types 646%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_646_step.
 - exact (prior 645%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_646 v sizes).
 - exact ran.
Qed.
Lemma global_progress_647 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;15] 4 final=Some (Gval (Fuint 1) (global_word_647 v)).
Proof.
 apply (global_sync_647_link invalid snapshot final v); [eapply global_progress_646; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_648 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;15] 25 final=Some (Gval (Fuint 1) (global_word_648 v)).
Proof.
 eapply global_node_648_step.
 - exact (prior 647%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_649 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 15 2 final=Some (Gval (Fuint 1) (global_word_649 v)).
Proof.
 have Typed := types 649%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_649_step.
 - exact (prior 31%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_649 v sizes).
 - exact ran.
Qed.
Lemma global_progress_650 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::15] 2 final=Some (Gval (Fuint 1) (global_word_650 v)).
Proof.
 apply (global_sync_650_link invalid snapshot final v); [eapply global_progress_649; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_651 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::15] 10 2 final=Some (Gval (Fuint 1) (global_word_651 v)).
Proof.
 have Typed := types 651%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_651_step.
 - exact (prior 650%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_651 v sizes).
 - exact ran.
Qed.
Lemma global_progress_652 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;15] 2 final=Some (Gval (Fuint 1) (global_word_652 v)).
Proof.
 apply (global_sync_652_link invalid snapshot final v); [eapply global_progress_651; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_653 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;15] 23 final=Some (Gval (Fuint 1) (global_word_653 v)).
Proof.
 eapply global_node_653_step.
 - exact (prior 652%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_654 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 15 3 final=Some (Gval (Fuint 1) (global_word_654 v)).
Proof.
 have Typed := types 654%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_654_step.
 - exact (prior 32%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_654 v sizes).
 - exact ran.
Qed.
Lemma global_progress_655 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::15] 3 final=Some (Gval (Fuint 1) (global_word_655 v)).
Proof.
 apply (global_sync_655_link invalid snapshot final v); [eapply global_progress_654; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_656 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::15] 10 3 final=Some (Gval (Fuint 1) (global_word_656 v)).
Proof.
 have Typed := types 656%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_656_step.
 - exact (prior 655%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_656 v sizes).
 - exact ran.
Qed.
Lemma global_progress_657 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;15] 3 final=Some (Gval (Fuint 1) (global_word_657 v)).
Proof.
 apply (global_sync_657_link invalid snapshot final v); [eapply global_progress_656; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_658 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;15] 24 final=Some (Gval (Fuint 1) (global_word_658 v)).
Proof.
 eapply global_node_658_step.
 - exact (prior 657%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_659 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;15] 26 final=Some (Gval (Fuint 1) (global_word_659 v)).
Proof.
 eapply global_node_659_step.
 - exact (prior 653%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 658%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_660 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(7 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;15] 28 final=Some (Gval (Fuint 1) (global_word_660 v)).
Proof.
 eapply global_node_660_step.
 - exact (prior 648%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 659%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_661 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;15] 27 final=Some (Gval (Fuint 1) (global_word_661 v)).
Proof.
 eapply global_node_661_step.
 - exact (prior 653%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 658%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_662 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(7 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;15] 29 final=Some (Gval (Fuint 1) (global_word_662 v)).
Proof.
 eapply global_node_662_step.
 - exact (prior 648%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 659%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_663 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(8 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;15] 30 final=Some (Gval (Fuint 1) (global_word_663 v)).
Proof.
 eapply global_node_663_step.
 - exact (prior 661%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact (prior 662%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (7 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_664 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(9 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;15] 31 final=Some (Gval (Fuint 2) (global_word_664 v)).
Proof.
 eapply global_node_664_step.
 - exact (prior 660%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (7 <= level)%coq_nat; lia))).
 - exact (prior 663%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (8 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_665 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(10 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;15] 32 final=Some (Gval (Fuint 2) (global_word_665 v)).
Proof.
 eapply global_node_665_step.
 - exact (prior 664%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (9 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_666 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(11 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;15] 33 final=Some (Gval (Fuint 1) (global_word_666 v)).
Proof.
 eapply global_node_666_step.
 - exact (prior 665%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (10 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_667.
Lemma global_connect_667_alias v : global_word_667 v = global_word_666 v.
Proof. unfold global_word_667, global_closed_667, global_expr_667, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_667.
Lemma global_progress_667 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(12 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;15] 5 final=Some (Gval (Fuint 1) (global_word_667 v)).
Proof.
 have Typed := types 667%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_667_step.
 - exact (prior 666%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (11 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_667_alias. apply adapt_uint_same. exact (global_size_666 v sizes).
 - exact ran.
Qed.
Lemma global_progress_668 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::15] 10 5 final=Some (Gval (Fuint 1) (global_word_668 v)).
Proof.
 apply (global_sync_668_link invalid snapshot final v); [eapply global_progress_667; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_669 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::15] 38 final=Some (Gval (Fuint 1) (global_word_669 v)).
Proof.
 eapply global_node_669_step.
 - exact (prior 668%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_670 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::15] 11 2 final=Some (Gval (Fuint 1) (global_word_670 v)).
Proof.
 have Typed := types 670%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_670_step.
 - exact (prior 669%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_670 v sizes).
 - exact ran.
Qed.
Lemma global_progress_671 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;15] 2 final=Some (Gval (Fuint 1) (global_word_671 v)).
Proof.
 apply (global_sync_671_link invalid snapshot final v); [eapply global_progress_670; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_672 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(17 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;15] 23 final=Some (Gval (Fuint 1) (global_word_672 v)).
Proof.
 eapply global_node_672_step.
 - exact (prior 671%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_673 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 15 5 final=Some (Gval (Fuint 1) (global_word_673 v)).
Proof.
 have Typed := types 673%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_673_step.
 - exact (prior 34%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_673 v sizes).
 - exact ran.
Qed.
Lemma global_progress_674 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::15] 5 final=Some (Gval (Fuint 1) (global_word_674 v)).
Proof.
 apply (global_sync_674_link invalid snapshot final v); [eapply global_progress_673; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_675 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::15] 39 final=Some (Gval (Fuint 1) (global_word_675 v)).
Proof.
 eapply global_node_675_step.
 - exact (prior 674%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_676 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::15] 11 3 final=Some (Gval (Fuint 1) (global_word_676 v)).
Proof.
 have Typed := types 676%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_676_step.
 - exact (prior 675%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_676 v sizes).
 - exact ran.
Qed.
Lemma global_progress_677 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;15] 3 final=Some (Gval (Fuint 1) (global_word_677 v)).
Proof.
 apply (global_sync_677_link invalid snapshot final v); [eapply global_progress_676; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_678 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;15] 24 final=Some (Gval (Fuint 1) (global_word_678 v)).
Proof.
 eapply global_node_678_step.
 - exact (prior 677%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_679 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;15] 26 final=Some (Gval (Fuint 1) (global_word_679 v)).
Proof.
 eapply global_node_679_step.
 - exact (prior 672%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact (prior 678%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_680 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(24 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;15] 28 final=Some (Gval (Fuint 1) (global_word_680 v)).
Proof.
 eapply global_node_680_step.
 - exact (prior 643%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (23 <= level)%coq_nat; lia))).
 - exact (prior 679%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_681 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;15] 27 final=Some (Gval (Fuint 1) (global_word_681 v)).
Proof.
 eapply global_node_681_step.
 - exact (prior 672%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact (prior 678%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_682 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(24 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;15] 29 final=Some (Gval (Fuint 1) (global_word_682 v)).
Proof.
 eapply global_node_682_step.
 - exact (prior 643%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (23 <= level)%coq_nat; lia))).
 - exact (prior 679%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_683 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(25 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;15] 30 final=Some (Gval (Fuint 1) (global_word_683 v)).
Proof.
 eapply global_node_683_step.
 - exact (prior 681%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact (prior 682%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (24 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_684 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(26 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;15] 31 final=Some (Gval (Fuint 2) (global_word_684 v)).
Proof.
 eapply global_node_684_step.
 - exact (prior 680%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (24 <= level)%coq_nat; lia))).
 - exact (prior 683%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (25 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_685 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(27 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;15] 32 final=Some (Gval (Fuint 2) (global_word_685 v)).
Proof.
 eapply global_node_685_step.
 - exact (prior 684%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (26 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_686 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(28 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;15] 33 final=Some (Gval (Fuint 1) (global_word_686 v)).
Proof.
 eapply global_node_686_step.
 - exact (prior 685%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (27 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_687.
Lemma global_connect_687_alias v : global_word_687 v = global_word_686 v.
Proof. unfold global_word_687, global_closed_687, global_expr_687, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_687.
Lemma global_progress_687 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(29 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;15] 5 final=Some (Gval (Fuint 1) (global_word_687 v)).
Proof.
 have Typed := types 687%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_687_step.
 - exact (prior 686%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (28 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_687_alias. apply adapt_uint_same. exact (global_size_686 v sizes).
 - exact ran.
Qed.
Lemma global_progress_688 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(30 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::15] 11 5 final=Some (Gval (Fuint 1) (global_word_688 v)).
Proof.
 apply (global_sync_688_link invalid snapshot final v); [eapply global_progress_687; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_689 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(31 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::15] 41 final=Some (Gval (Fuint 1) (global_word_689 v)).
Proof.
 eapply global_node_689_step.
 - exact (prior 688%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (30 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_690.
Lemma global_connect_690_alias v : global_word_690 v = global_word_689 v.
Proof. unfold global_word_690, global_closed_690, global_expr_690, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_690.
Lemma global_progress_690 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(32 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::15] 7 final=Some (Gval (Fuint 1) (global_word_690 v)).
Proof.
 have Typed := types 690%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_690_step.
 - exact (prior 689%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (31 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_690_alias. apply adapt_uint_same. exact (global_size_689 v sizes).
 - exact ran.
Qed.
Lemma global_progress_691 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(33 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 15 7 final=Some (Gval (Fuint 1) (global_word_691 v)).
Proof.
 apply (global_sync_691_link invalid snapshot final v); [eapply global_progress_690; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_692 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(34 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 325 final=Some (Gval (Fuint 1) (global_word_692 v)).
Proof.
 eapply global_node_692_step.
 - exact (prior 691%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (33 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_693 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(11 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;15] 34 final=Some (Gval (Fuint 1) (global_word_693 v)).
Proof.
 eapply global_node_693_step.
 - exact (prior 665%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (10 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_694.
Lemma global_connect_694_alias v : global_word_694 v = global_word_693 v.
Proof. unfold global_word_694, global_closed_694, global_expr_694, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_694.
Lemma global_progress_694 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(12 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;15] 6 final=Some (Gval (Fuint 1) (global_word_694 v)).
Proof.
 have Typed := types 694%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_694_step.
 - exact (prior 693%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (11 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_694_alias. apply adapt_uint_same. exact (global_size_693 v sizes).
 - exact ran.
Qed.
Lemma global_progress_695 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::15] 10 6 final=Some (Gval (Fuint 1) (global_word_695 v)).
Proof.
 apply (global_sync_695_link invalid snapshot final v); [eapply global_progress_694; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_696 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::15] 42 final=Some (Gval (Fuint 1) (global_word_696 v)).
Proof.
 eapply global_node_696_step.
 - exact (prior 695%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_697.
Lemma global_connect_697_alias v : global_word_697 v = global_word_696 v.
Proof. unfold global_word_697, global_closed_697, global_expr_697, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_697.
Lemma global_progress_697 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::15] 8 final=Some (Gval (Fuint 1) (global_word_697 v)).
Proof.
 have Typed := types 697%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_697_step.
 - exact (prior 696%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_697_alias. apply adapt_uint_same. exact (global_size_696 v sizes).
 - exact ran.
Qed.
Lemma global_progress_698 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 15 8 final=Some (Gval (Fuint 1) (global_word_698 v)).
Proof.
 apply (global_sync_698_link invalid snapshot final v); [eapply global_progress_697; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_699 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(17 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 326 final=Some (Gval (Fuint 1) (global_word_699 v)).
Proof.
 eapply global_node_699_step.
 - exact (prior 698%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_700 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(28 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;15] 34 final=Some (Gval (Fuint 1) (global_word_700 v)).
Proof.
 eapply global_node_700_step.
 - exact (prior 685%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (27 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_701.
Lemma global_connect_701_alias v : global_word_701 v = global_word_700 v.
Proof. unfold global_word_701, global_closed_701, global_expr_701, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_701.
Lemma global_progress_701 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(29 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;15] 6 final=Some (Gval (Fuint 1) (global_word_701 v)).
Proof.
 have Typed := types 701%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_701_step.
 - exact (prior 700%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (28 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_701_alias. apply adapt_uint_same. exact (global_size_700 v sizes).
 - exact ran.
Qed.
Lemma global_progress_702 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(30 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::15] 11 6 final=Some (Gval (Fuint 1) (global_word_702 v)).
Proof.
 apply (global_sync_702_link invalid snapshot final v); [eapply global_progress_701; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_703 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(31 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::15] 43 final=Some (Gval (Fuint 1) (global_word_703 v)).
Proof.
 eapply global_node_703_step.
 - exact (prior 702%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (30 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_704.
Lemma global_connect_704_alias v : global_word_704 v = global_word_703 v.
Proof. unfold global_word_704, global_closed_704, global_expr_704, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_704.
Lemma global_progress_704 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(32 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::15] 9 final=Some (Gval (Fuint 1) (global_word_704 v)).
Proof.
 have Typed := types 704%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_704_step.
 - exact (prior 703%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (31 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_704_alias. apply adapt_uint_same. exact (global_size_703 v sizes).
 - exact ran.
Qed.
Lemma global_progress_705 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(33 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 15 9 final=Some (Gval (Fuint 1) (global_word_705 v)).
Proof.
 apply (global_sync_705_link invalid snapshot final v); [eapply global_progress_704; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_706 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(34 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 327 final=Some (Gval (Fuint 1) (global_word_706 v)).
Proof.
 eapply global_node_706_step.
 - exact (prior 705%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (33 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_707 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 16 6 final=Some (Gval (Fuint 1) (global_word_707 v)).
Proof.
 have Typed := types 707%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_707_step.
 - exact (prior 699%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_707 v sizes).
 - exact ran.
Qed.
Lemma global_progress_708 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(19 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::16] 6 final=Some (Gval (Fuint 1) (global_word_708 v)).
Proof.
 apply (global_sync_708_link invalid snapshot final v); [eapply global_progress_707; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_709 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(20 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::16] 40 final=Some (Gval (Fuint 1) (global_word_709 v)).
Proof.
 eapply global_node_709_step.
 - exact (prior 708%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (19 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_710 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(21 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::16] 11 4 final=Some (Gval (Fuint 1) (global_word_710 v)).
Proof.
 have Typed := types 710%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_710_step.
 - exact (prior 709%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (20 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_710 v sizes).
 - exact ran.
Qed.
Lemma global_progress_711 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(22 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 4 final=Some (Gval (Fuint 1) (global_word_711 v)).
Proof.
 apply (global_sync_711_link invalid snapshot final v); [eapply global_progress_710; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_712 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(23 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 25 final=Some (Gval (Fuint 1) (global_word_712 v)).
Proof.
 eapply global_node_712_step.
 - exact (prior 711%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (22 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_713 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 16 4 final=Some (Gval (Fuint 1) (global_word_713 v)).
Proof.
 have Typed := types 713%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_713_step.
 - exact (prior 37%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_713 v sizes).
 - exact ran.
Qed.
Lemma global_progress_714 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::16] 4 final=Some (Gval (Fuint 1) (global_word_714 v)).
Proof.
 apply (global_sync_714_link invalid snapshot final v); [eapply global_progress_713; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_715 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::16] 10 4 final=Some (Gval (Fuint 1) (global_word_715 v)).
Proof.
 have Typed := types 715%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_715_step.
 - exact (prior 714%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_715 v sizes).
 - exact ran.
Qed.
Lemma global_progress_716 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 4 final=Some (Gval (Fuint 1) (global_word_716 v)).
Proof.
 apply (global_sync_716_link invalid snapshot final v); [eapply global_progress_715; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_717 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 25 final=Some (Gval (Fuint 1) (global_word_717 v)).
Proof.
 eapply global_node_717_step.
 - exact (prior 716%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_718 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 16 2 final=Some (Gval (Fuint 1) (global_word_718 v)).
Proof.
 have Typed := types 718%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_718_step.
 - exact (prior 35%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_718 v sizes).
 - exact ran.
Qed.
Lemma global_progress_719 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::16] 2 final=Some (Gval (Fuint 1) (global_word_719 v)).
Proof.
 apply (global_sync_719_link invalid snapshot final v); [eapply global_progress_718; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_720 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::16] 10 2 final=Some (Gval (Fuint 1) (global_word_720 v)).
Proof.
 have Typed := types 720%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_720_step.
 - exact (prior 719%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_720 v sizes).
 - exact ran.
Qed.
Lemma global_progress_721 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 2 final=Some (Gval (Fuint 1) (global_word_721 v)).
Proof.
 apply (global_sync_721_link invalid snapshot final v); [eapply global_progress_720; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_722 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 23 final=Some (Gval (Fuint 1) (global_word_722 v)).
Proof.
 eapply global_node_722_step.
 - exact (prior 721%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_723 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 16 3 final=Some (Gval (Fuint 1) (global_word_723 v)).
Proof.
 have Typed := types 723%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_723_step.
 - exact (prior 36%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_723 v sizes).
 - exact ran.
Qed.
Lemma global_progress_724 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::16] 3 final=Some (Gval (Fuint 1) (global_word_724 v)).
Proof.
 apply (global_sync_724_link invalid snapshot final v); [eapply global_progress_723; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_725 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::16] 10 3 final=Some (Gval (Fuint 1) (global_word_725 v)).
Proof.
 have Typed := types 725%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_725_step.
 - exact (prior 724%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_725 v sizes).
 - exact ran.
Qed.
Lemma global_progress_726 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 3 final=Some (Gval (Fuint 1) (global_word_726 v)).
Proof.
 apply (global_sync_726_link invalid snapshot final v); [eapply global_progress_725; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_727 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 24 final=Some (Gval (Fuint 1) (global_word_727 v)).
Proof.
 eapply global_node_727_step.
 - exact (prior 726%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_728 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 26 final=Some (Gval (Fuint 1) (global_word_728 v)).
Proof.
 eapply global_node_728_step.
 - exact (prior 722%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 727%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_729 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(7 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 28 final=Some (Gval (Fuint 1) (global_word_729 v)).
Proof.
 eapply global_node_729_step.
 - exact (prior 717%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 728%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_730 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 27 final=Some (Gval (Fuint 1) (global_word_730 v)).
Proof.
 eapply global_node_730_step.
 - exact (prior 722%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 727%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_731 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(7 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 29 final=Some (Gval (Fuint 1) (global_word_731 v)).
Proof.
 eapply global_node_731_step.
 - exact (prior 717%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 728%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_732 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(8 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 30 final=Some (Gval (Fuint 1) (global_word_732 v)).
Proof.
 eapply global_node_732_step.
 - exact (prior 730%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact (prior 731%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (7 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_733 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(9 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 31 final=Some (Gval (Fuint 2) (global_word_733 v)).
Proof.
 eapply global_node_733_step.
 - exact (prior 729%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (7 <= level)%coq_nat; lia))).
 - exact (prior 732%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (8 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_734 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(10 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 32 final=Some (Gval (Fuint 2) (global_word_734 v)).
Proof.
 eapply global_node_734_step.
 - exact (prior 733%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (9 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_735 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(11 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 33 final=Some (Gval (Fuint 1) (global_word_735 v)).
Proof.
 eapply global_node_735_step.
 - exact (prior 734%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (10 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_736.
Lemma global_connect_736_alias v : global_word_736 v = global_word_735 v.
Proof. unfold global_word_736, global_closed_736, global_expr_736, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_736.
Lemma global_progress_736 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(12 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 5 final=Some (Gval (Fuint 1) (global_word_736 v)).
Proof.
 have Typed := types 736%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_736_step.
 - exact (prior 735%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (11 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_736_alias. apply adapt_uint_same. exact (global_size_735 v sizes).
 - exact ran.
Qed.
Lemma global_progress_737 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::16] 10 5 final=Some (Gval (Fuint 1) (global_word_737 v)).
Proof.
 apply (global_sync_737_link invalid snapshot final v); [eapply global_progress_736; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_738 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::16] 38 final=Some (Gval (Fuint 1) (global_word_738 v)).
Proof.
 eapply global_node_738_step.
 - exact (prior 737%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_739 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::16] 11 2 final=Some (Gval (Fuint 1) (global_word_739 v)).
Proof.
 have Typed := types 739%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_739_step.
 - exact (prior 738%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_739 v sizes).
 - exact ran.
Qed.
Lemma global_progress_740 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 2 final=Some (Gval (Fuint 1) (global_word_740 v)).
Proof.
 apply (global_sync_740_link invalid snapshot final v); [eapply global_progress_739; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_741 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(17 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 23 final=Some (Gval (Fuint 1) (global_word_741 v)).
Proof.
 eapply global_node_741_step.
 - exact (prior 740%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_742 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 16 5 final=Some (Gval (Fuint 1) (global_word_742 v)).
Proof.
 have Typed := types 742%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_742_step.
 - exact (prior 38%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_742 v sizes).
 - exact ran.
Qed.
Lemma global_progress_743 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::16] 5 final=Some (Gval (Fuint 1) (global_word_743 v)).
Proof.
 apply (global_sync_743_link invalid snapshot final v); [eapply global_progress_742; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_744 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::16] 39 final=Some (Gval (Fuint 1) (global_word_744 v)).
Proof.
 eapply global_node_744_step.
 - exact (prior 743%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_745 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::16] 11 3 final=Some (Gval (Fuint 1) (global_word_745 v)).
Proof.
 have Typed := types 745%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_745_step.
 - exact (prior 744%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_745 v sizes).
 - exact ran.
Qed.
Lemma global_progress_746 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 3 final=Some (Gval (Fuint 1) (global_word_746 v)).
Proof.
 apply (global_sync_746_link invalid snapshot final v); [eapply global_progress_745; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_747 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 24 final=Some (Gval (Fuint 1) (global_word_747 v)).
Proof.
 eapply global_node_747_step.
 - exact (prior 746%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_748 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 26 final=Some (Gval (Fuint 1) (global_word_748 v)).
Proof.
 eapply global_node_748_step.
 - exact (prior 741%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact (prior 747%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_749 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(24 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 28 final=Some (Gval (Fuint 1) (global_word_749 v)).
Proof.
 eapply global_node_749_step.
 - exact (prior 712%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (23 <= level)%coq_nat; lia))).
 - exact (prior 748%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_750 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 27 final=Some (Gval (Fuint 1) (global_word_750 v)).
Proof.
 eapply global_node_750_step.
 - exact (prior 741%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact (prior 747%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_751 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(24 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 29 final=Some (Gval (Fuint 1) (global_word_751 v)).
Proof.
 eapply global_node_751_step.
 - exact (prior 712%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (23 <= level)%coq_nat; lia))).
 - exact (prior 748%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_752 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(25 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 30 final=Some (Gval (Fuint 1) (global_word_752 v)).
Proof.
 eapply global_node_752_step.
 - exact (prior 750%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (18 <= level)%coq_nat; lia))).
 - exact (prior 751%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (24 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_753 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(26 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 31 final=Some (Gval (Fuint 2) (global_word_753 v)).
Proof.
 eapply global_node_753_step.
 - exact (prior 749%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (24 <= level)%coq_nat; lia))).
 - exact (prior 752%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (25 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_754 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(27 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 32 final=Some (Gval (Fuint 2) (global_word_754 v)).
Proof.
 eapply global_node_754_step.
 - exact (prior 753%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (26 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_755 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(28 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 33 final=Some (Gval (Fuint 1) (global_word_755 v)).
Proof.
 eapply global_node_755_step.
 - exact (prior 754%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (27 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_756.
Lemma global_connect_756_alias v : global_word_756 v = global_word_755 v.
Proof. unfold global_word_756, global_closed_756, global_expr_756, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_756.
Lemma global_progress_756 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(29 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 5 final=Some (Gval (Fuint 1) (global_word_756 v)).
Proof.
 have Typed := types 756%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_756_step.
 - exact (prior 755%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (28 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_756_alias. apply adapt_uint_same. exact (global_size_755 v sizes).
 - exact ran.
Qed.
Lemma global_progress_757 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(30 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::16] 11 5 final=Some (Gval (Fuint 1) (global_word_757 v)).
Proof.
 apply (global_sync_757_link invalid snapshot final v); [eapply global_progress_756; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_758 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(31 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::16] 41 final=Some (Gval (Fuint 1) (global_word_758 v)).
Proof.
 eapply global_node_758_step.
 - exact (prior 757%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (30 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_759.
Lemma global_connect_759_alias v : global_word_759 v = global_word_758 v.
Proof. unfold global_word_759, global_closed_759, global_expr_759, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_759.
Lemma global_progress_759 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(32 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::16] 7 final=Some (Gval (Fuint 1) (global_word_759 v)).
Proof.
 have Typed := types 759%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_759_step.
 - exact (prior 758%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (31 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_759_alias. apply adapt_uint_same. exact (global_size_758 v sizes).
 - exact ran.
Qed.
Lemma global_progress_760 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(33 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 16 7 final=Some (Gval (Fuint 1) (global_word_760 v)).
Proof.
 apply (global_sync_760_link invalid snapshot final v); [eapply global_progress_759; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_761 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(34 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 328 final=Some (Gval (Fuint 1) (global_word_761 v)).
Proof.
 eapply global_node_761_step.
 - exact (prior 760%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (33 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_762 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(11 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 34 final=Some (Gval (Fuint 1) (global_word_762 v)).
Proof.
 eapply global_node_762_step.
 - exact (prior 734%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (10 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_763.
Lemma global_connect_763_alias v : global_word_763 v = global_word_762 v.
Proof. unfold global_word_763, global_closed_763, global_expr_763, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_763.
Lemma global_progress_763 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(12 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 6 final=Some (Gval (Fuint 1) (global_word_763 v)).
Proof.
 have Typed := types 763%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_763_step.
 - exact (prior 762%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (11 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_763_alias. apply adapt_uint_same. exact (global_size_762 v sizes).
 - exact ran.
Qed.
Lemma global_progress_764 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::16] 10 6 final=Some (Gval (Fuint 1) (global_word_764 v)).
Proof.
 apply (global_sync_764_link invalid snapshot final v); [eapply global_progress_763; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_765 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::16] 42 final=Some (Gval (Fuint 1) (global_word_765 v)).
Proof.
 eapply global_node_765_step.
 - exact (prior 764%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_766.
Lemma global_connect_766_alias v : global_word_766 v = global_word_765 v.
Proof. unfold global_word_766, global_closed_766, global_expr_766, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_766.
Lemma global_progress_766 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::16] 8 final=Some (Gval (Fuint 1) (global_word_766 v)).
Proof.
 have Typed := types 766%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_766_step.
 - exact (prior 765%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_766_alias. apply adapt_uint_same. exact (global_size_765 v sizes).
 - exact ran.
Qed.
Lemma global_progress_767 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 16 8 final=Some (Gval (Fuint 1) (global_word_767 v)).
Proof.
 apply (global_sync_767_link invalid snapshot final v); [eapply global_progress_766; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_768 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(17 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 329 final=Some (Gval (Fuint 1) (global_word_768 v)).
Proof.
 eapply global_node_768_step.
 - exact (prior 767%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_769 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(28 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 34 final=Some (Gval (Fuint 1) (global_word_769 v)).
Proof.
 eapply global_node_769_step.
 - exact (prior 754%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (27 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_770.
Lemma global_connect_770_alias v : global_word_770 v = global_word_769 v.
Proof. unfold global_word_770, global_closed_770, global_expr_770, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_770.
Lemma global_progress_770 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(29 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 6 final=Some (Gval (Fuint 1) (global_word_770 v)).
Proof.
 have Typed := types 770%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_770_step.
 - exact (prior 769%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (28 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_770_alias. apply adapt_uint_same. exact (global_size_769 v sizes).
 - exact ran.
Qed.
Lemma global_progress_771 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(30 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::16] 11 6 final=Some (Gval (Fuint 1) (global_word_771 v)).
Proof.
 apply (global_sync_771_link invalid snapshot final v); [eapply global_progress_770; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_772 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(31 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::16] 43 final=Some (Gval (Fuint 1) (global_word_772 v)).
Proof.
 eapply global_node_772_step.
 - exact (prior 771%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (30 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_773.
Lemma global_connect_773_alias v : global_word_773 v = global_word_772 v.
Proof. unfold global_word_773, global_closed_773, global_expr_773, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_773.
Lemma global_progress_773 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(32 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::16] 9 final=Some (Gval (Fuint 1) (global_word_773 v)).
Proof.
 have Typed := types 773%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_773_step.
 - exact (prior 772%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (31 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_773_alias. apply adapt_uint_same. exact (global_size_772 v sizes).
 - exact ran.
Qed.
Lemma global_progress_774 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(33 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 16 9 final=Some (Gval (Fuint 1) (global_word_774 v)).
Proof.
 apply (global_sync_774_link invalid snapshot final v); [eapply global_progress_773; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_775 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(34 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 330 final=Some (Gval (Fuint 1) (global_word_775 v)).
Proof.
 eapply global_node_775_step.
 - exact (prior 774%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (33 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_776 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(18 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 17 6 final=Some (Gval (Fuint 1) (global_word_776 v)).
Proof.
 have Typed := types 776%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_776_step.
 - exact (prior 768%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (17 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_776 v sizes).
 - exact ran.
Qed.
Lemma global_progress_777 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(19 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 6 final=Some (Gval (Fuint 1) (global_word_777 v)).
Proof.
 apply (global_sync_777_link invalid snapshot final v); [eapply global_progress_776; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_778 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(20 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 40 final=Some (Gval (Fuint 1) (global_word_778 v)).
Proof.
 eapply global_node_778_step.
 - exact (prior 777%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (19 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_779 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(21 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::17] 11 4 final=Some (Gval (Fuint 1) (global_word_779 v)).
Proof.
 have Typed := types 779%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_779_step.
 - exact (prior 778%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (20 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_779 v sizes).
 - exact ran.
Qed.
Lemma global_progress_780 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(22 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 4 final=Some (Gval (Fuint 1) (global_word_780 v)).
Proof.
 apply (global_sync_780_link invalid snapshot final v); [eapply global_progress_779; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_781 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(23 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 25 final=Some (Gval (Fuint 1) (global_word_781 v)).
Proof.
 eapply global_node_781_step.
 - exact (prior 780%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (22 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_782 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 17 4 final=Some (Gval (Fuint 1) (global_word_782 v)).
Proof.
 have Typed := types 782%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_782_step.
 - exact (prior 41%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_782 v sizes).
 - exact ran.
Qed.
Lemma global_progress_783 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 4 final=Some (Gval (Fuint 1) (global_word_783 v)).
Proof.
 apply (global_sync_783_link invalid snapshot final v); [eapply global_progress_782; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_784 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::17] 10 4 final=Some (Gval (Fuint 1) (global_word_784 v)).
Proof.
 have Typed := types 784%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_784_step.
 - exact (prior 783%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_784 v sizes).
 - exact ran.
Qed.
Lemma global_progress_785 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 4 final=Some (Gval (Fuint 1) (global_word_785 v)).
Proof.
 apply (global_sync_785_link invalid snapshot final v); [eapply global_progress_784; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_786 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 25 final=Some (Gval (Fuint 1) (global_word_786 v)).
Proof.
 eapply global_node_786_step.
 - exact (prior 785%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_787 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 17 2 final=Some (Gval (Fuint 1) (global_word_787 v)).
Proof.
 have Typed := types 787%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_787_step.
 - exact (prior 39%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_787 v sizes).
 - exact ran.
Qed.
Lemma global_progress_788 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 2 final=Some (Gval (Fuint 1) (global_word_788 v)).
Proof.
 apply (global_sync_788_link invalid snapshot final v); [eapply global_progress_787; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_789 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::17] 10 2 final=Some (Gval (Fuint 1) (global_word_789 v)).
Proof.
 have Typed := types 789%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_789_step.
 - exact (prior 788%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_789 v sizes).
 - exact ran.
Qed.
Lemma global_progress_790 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 2 final=Some (Gval (Fuint 1) (global_word_790 v)).
Proof.
 apply (global_sync_790_link invalid snapshot final v); [eapply global_progress_789; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_791 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 23 final=Some (Gval (Fuint 1) (global_word_791 v)).
Proof.
 eapply global_node_791_step.
 - exact (prior 790%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_792 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 17 3 final=Some (Gval (Fuint 1) (global_word_792 v)).
Proof.
 have Typed := types 792%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_792_step.
 - exact (prior 40%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_792 v sizes).
 - exact ran.
Qed.
Lemma global_progress_793 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 3 final=Some (Gval (Fuint 1) (global_word_793 v)).
Proof.
 apply (global_sync_793_link invalid snapshot final v); [eapply global_progress_792; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_794 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::17] 10 3 final=Some (Gval (Fuint 1) (global_word_794 v)).
Proof.
 have Typed := types 794%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_794_step.
 - exact (prior 793%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_794 v sizes).
 - exact ran.
Qed.
Lemma global_progress_795 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 3 final=Some (Gval (Fuint 1) (global_word_795 v)).
Proof.
 apply (global_sync_795_link invalid snapshot final v); [eapply global_progress_794; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_796 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 24 final=Some (Gval (Fuint 1) (global_word_796 v)).
Proof.
 eapply global_node_796_step.
 - exact (prior 795%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_797 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 26 final=Some (Gval (Fuint 1) (global_word_797 v)).
Proof.
 eapply global_node_797_step.
 - exact (prior 791%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 796%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_798 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(7 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 28 final=Some (Gval (Fuint 1) (global_word_798 v)).
Proof.
 eapply global_node_798_step.
 - exact (prior 786%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 797%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_799 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 27 final=Some (Gval (Fuint 1) (global_word_799 v)).
Proof.
 eapply global_node_799_step.
 - exact (prior 791%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 796%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
