From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import InitialMapFacts InitialInstanceFacts CircuitInitialFacts HierarchyFacts PortFieldFacts.
From SmallMultiplier Require Import Model GlobalStable GlobalInstances GlobalProgressTypes GlobalInitialLocal.
Local Open Scope N_scope.
Local Opaque statements_initial_map_with_memory circuit_initial_map_with_memory.
Lemma multiplier_initial_root v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 exists env,statements_initial_map_with_memory generated_modules generated_module_3_stmts_0
 (match previous with Some maps=>SVM.find [::] maps|None=>None end) (ports_initial_map(multiplier_ports 3))=Some env /\ SVM.find [::] states=Some(multiplier_externalized v env).
Proof.
 destruct (circuit_initial_root generated_modules generated_top previous external states multiplier_instances (multiplier_ports 3) generated_module_3_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) ran) as [before [after [Initial [External Found]]]].
 rewrite (multiplier_external_update v before external ports) in External. inversion External;subst after.
 exists before;split;assumption.
Qed.
Lemma initial_leaf_0 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 0%nat states=Some(global_target_at 0%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 0 states=Some(Gval Fclock (global_word_0 v))).
 unfold circuit_lookup. rewrite Found.
 apply multiplier_external_0.
Qed.
Lemma initial_leaf_1 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 1%nat states=Some(global_target_at 1%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 1 states=Some(Gval (Fuint 1) (global_word_1 v))).
 unfold circuit_lookup. rewrite Found.
 apply multiplier_external_1.
Qed.
Lemma initial_leaf_2 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 2%nat states=Some(global_target_at 2%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 2 states=Some(Gval (Fuint 8) (global_word_2 v))).
 unfold circuit_lookup. rewrite Found.
 apply multiplier_external_2.
Qed.
Lemma initial_leaf_3 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 3%nat states=Some(global_target_at 3%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 201 states=Some(Gval (Fuint 1) (global_word_3 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 201 (ltac:(reflexivity))).
 have Known := registers 3%nat (ltac:(simpl;tauto)).
 change (VM.find 201 old=Some(Gval (Fuint 1) (global_word_3 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 201 _ generated_module_3_stmts_0 Known initial_register_201); exact Initial.
Qed.
Lemma initial_leaf_4 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 4%nat states=Some(global_target_at 4%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 203 states=Some(Gval (Fuint 1) (global_word_4 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 203 (ltac:(reflexivity))).
 have Known := registers 4%nat (ltac:(simpl;tauto)).
 change (VM.find 203 old=Some(Gval (Fuint 1) (global_word_4 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 203 _ generated_module_3_stmts_0 Known initial_register_203); exact Initial.
Qed.
Lemma initial_leaf_5 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 5%nat states=Some(global_target_at 5%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 205 states=Some(Gval (Fuint 1) (global_word_5 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 205 (ltac:(reflexivity))).
 have Known := registers 5%nat (ltac:(simpl;tauto)).
 change (VM.find 205 old=Some(Gval (Fuint 1) (global_word_5 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 205 _ generated_module_3_stmts_0 Known initial_register_205); exact Initial.
Qed.
Lemma initial_leaf_6 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 6%nat states=Some(global_target_at 6%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 207 states=Some(Gval (Fuint 1) (global_word_6 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 207 (ltac:(reflexivity))).
 have Known := registers 6%nat (ltac:(simpl;tauto)).
 change (VM.find 207 old=Some(Gval (Fuint 1) (global_word_6 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 207 _ generated_module_3_stmts_0 Known initial_register_207); exact Initial.
Qed.
Lemma initial_leaf_7 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 7%nat states=Some(global_target_at 7%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 209 states=Some(Gval (Fuint 1) (global_word_7 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 209 (ltac:(reflexivity))).
 have Known := registers 7%nat (ltac:(simpl;tauto)).
 change (VM.find 209 old=Some(Gval (Fuint 1) (global_word_7 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 209 _ generated_module_3_stmts_0 Known initial_register_209); exact Initial.
Qed.
Lemma initial_leaf_8 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 8%nat states=Some(global_target_at 8%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 211 states=Some(Gval (Fuint 1) (global_word_8 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 211 (ltac:(reflexivity))).
 have Known := registers 8%nat (ltac:(simpl;tauto)).
 change (VM.find 211 old=Some(Gval (Fuint 1) (global_word_8 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 211 _ generated_module_3_stmts_0 Known initial_register_211); exact Initial.
Qed.
Lemma initial_leaf_9 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 9%nat states=Some(global_target_at 9%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 213 states=Some(Gval (Fuint 1) (global_word_9 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 213 (ltac:(reflexivity))).
 have Known := registers 9%nat (ltac:(simpl;tauto)).
 change (VM.find 213 old=Some(Gval (Fuint 1) (global_word_9 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 213 _ generated_module_3_stmts_0 Known initial_register_213); exact Initial.
Qed.
Lemma initial_leaf_10 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 10%nat states=Some(global_target_at 10%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 215 states=Some(Gval (Fuint 1) (global_word_10 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 215 (ltac:(reflexivity))).
 have Known := registers 10%nat (ltac:(simpl;tauto)).
 change (VM.find 215 old=Some(Gval (Fuint 1) (global_word_10 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 215 _ generated_module_3_stmts_0 Known initial_register_215); exact Initial.
Qed.
Lemma initial_leaf_11 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 11%nat states=Some(global_target_at 11%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 217 states=Some(Gval (Fuint 1) (global_word_11 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 217 (ltac:(reflexivity))).
 have Known := registers 11%nat (ltac:(simpl;tauto)).
 change (VM.find 217 old=Some(Gval (Fuint 1) (global_word_11 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 217 _ generated_module_3_stmts_0 Known initial_register_217); exact Initial.
Qed.
Lemma initial_leaf_12 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 12%nat states=Some(global_target_at 12%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 219 states=Some(Gval (Fuint 1) (global_word_12 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 219 (ltac:(reflexivity))).
 have Known := registers 12%nat (ltac:(simpl;tauto)).
 change (VM.find 219 old=Some(Gval (Fuint 1) (global_word_12 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 219 _ generated_module_3_stmts_0 Known initial_register_219); exact Initial.
Qed.
Lemma initial_leaf_13 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 13%nat states=Some(global_target_at 13%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 221 states=Some(Gval (Fuint 1) (global_word_13 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 221 (ltac:(reflexivity))).
 have Known := registers 13%nat (ltac:(simpl;tauto)).
 change (VM.find 221 old=Some(Gval (Fuint 1) (global_word_13 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 221 _ generated_module_3_stmts_0 Known initial_register_221); exact Initial.
Qed.
Lemma initial_leaf_14 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 14%nat states=Some(global_target_at 14%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 223 states=Some(Gval (Fuint 1) (global_word_14 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 223 (ltac:(reflexivity))).
 have Known := registers 14%nat (ltac:(simpl;tauto)).
 change (VM.find 223 old=Some(Gval (Fuint 1) (global_word_14 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 223 _ generated_module_3_stmts_0 Known initial_register_223); exact Initial.
Qed.
Lemma initial_leaf_15 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 15%nat states=Some(global_target_at 15%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 225 states=Some(Gval (Fuint 1) (global_word_15 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 225 (ltac:(reflexivity))).
 have Known := registers 15%nat (ltac:(simpl;tauto)).
 change (VM.find 225 old=Some(Gval (Fuint 1) (global_word_15 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 225 _ generated_module_3_stmts_0 Known initial_register_225); exact Initial.
Qed.
Lemma initial_leaf_16 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 16%nat states=Some(global_target_at 16%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 227 states=Some(Gval (Fuint 1) (global_word_16 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 227 (ltac:(reflexivity))).
 have Known := registers 16%nat (ltac:(simpl;tauto)).
 change (VM.find 227 old=Some(Gval (Fuint 1) (global_word_16 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 227 _ generated_module_3_stmts_0 Known initial_register_227); exact Initial.
Qed.
Lemma initial_leaf_17 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 17%nat states=Some(global_target_at 17%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 229 states=Some(Gval (Fuint 1) (global_word_17 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 229 (ltac:(reflexivity))).
 have Known := registers 17%nat (ltac:(simpl;tauto)).
 change (VM.find 229 old=Some(Gval (Fuint 1) (global_word_17 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 229 _ generated_module_3_stmts_0 Known initial_register_229); exact Initial.
Qed.
Lemma initial_leaf_18 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 18%nat states=Some(global_target_at 18%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 231 states=Some(Gval (Fuint 1) (global_word_18 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 231 (ltac:(reflexivity))).
 have Known := registers 18%nat (ltac:(simpl;tauto)).
 change (VM.find 231 old=Some(Gval (Fuint 1) (global_word_18 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 231 _ generated_module_3_stmts_0 Known initial_register_231); exact Initial.
Qed.
Lemma initial_leaf_19 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 19%nat states=Some(global_target_at 19%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 233 states=Some(Gval (Fuint 1) (global_word_19 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 233 (ltac:(reflexivity))).
 have Known := registers 19%nat (ltac:(simpl;tauto)).
 change (VM.find 233 old=Some(Gval (Fuint 1) (global_word_19 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 233 _ generated_module_3_stmts_0 Known initial_register_233); exact Initial.
Qed.
Lemma initial_leaf_20 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 20%nat states=Some(global_target_at 20%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 235 states=Some(Gval (Fuint 1) (global_word_20 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 235 (ltac:(reflexivity))).
 have Known := registers 20%nat (ltac:(simpl;tauto)).
 change (VM.find 235 old=Some(Gval (Fuint 1) (global_word_20 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 235 _ generated_module_3_stmts_0 Known initial_register_235); exact Initial.
Qed.
Lemma initial_leaf_21 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 21%nat states=Some(global_target_at 21%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 237 states=Some(Gval (Fuint 1) (global_word_21 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 237 (ltac:(reflexivity))).
 have Known := registers 21%nat (ltac:(simpl;tauto)).
 change (VM.find 237 old=Some(Gval (Fuint 1) (global_word_21 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 237 _ generated_module_3_stmts_0 Known initial_register_237); exact Initial.
Qed.
Lemma initial_leaf_22 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 22%nat states=Some(global_target_at 22%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 239 states=Some(Gval (Fuint 1) (global_word_22 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 239 (ltac:(reflexivity))).
 have Known := registers 22%nat (ltac:(simpl;tauto)).
 change (VM.find 239 old=Some(Gval (Fuint 1) (global_word_22 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 239 _ generated_module_3_stmts_0 Known initial_register_239); exact Initial.
Qed.
Lemma initial_leaf_23 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 23%nat states=Some(global_target_at 23%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 241 states=Some(Gval (Fuint 1) (global_word_23 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 241 (ltac:(reflexivity))).
 have Known := registers 23%nat (ltac:(simpl;tauto)).
 change (VM.find 241 old=Some(Gval (Fuint 1) (global_word_23 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 241 _ generated_module_3_stmts_0 Known initial_register_241); exact Initial.
Qed.
Lemma initial_leaf_24 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 24%nat states=Some(global_target_at 24%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 243 states=Some(Gval (Fuint 1) (global_word_24 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 243 (ltac:(reflexivity))).
 have Known := registers 24%nat (ltac:(simpl;tauto)).
 change (VM.find 243 old=Some(Gval (Fuint 1) (global_word_24 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 243 _ generated_module_3_stmts_0 Known initial_register_243); exact Initial.
Qed.
Lemma initial_leaf_25 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 25%nat states=Some(global_target_at 25%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 245 states=Some(Gval (Fuint 1) (global_word_25 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 245 (ltac:(reflexivity))).
 have Known := registers 25%nat (ltac:(simpl;tauto)).
 change (VM.find 245 old=Some(Gval (Fuint 1) (global_word_25 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 245 _ generated_module_3_stmts_0 Known initial_register_245); exact Initial.
Qed.
Lemma initial_leaf_26 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 26%nat states=Some(global_target_at 26%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 247 states=Some(Gval (Fuint 1) (global_word_26 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 247 (ltac:(reflexivity))).
 have Known := registers 26%nat (ltac:(simpl;tauto)).
 change (VM.find 247 old=Some(Gval (Fuint 1) (global_word_26 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 247 _ generated_module_3_stmts_0 Known initial_register_247); exact Initial.
Qed.
Lemma initial_leaf_27 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 27%nat states=Some(global_target_at 27%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 249 states=Some(Gval (Fuint 1) (global_word_27 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 249 (ltac:(reflexivity))).
 have Known := registers 27%nat (ltac:(simpl;tauto)).
 change (VM.find 249 old=Some(Gval (Fuint 1) (global_word_27 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 249 _ generated_module_3_stmts_0 Known initial_register_249); exact Initial.
Qed.
Lemma initial_leaf_28 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 28%nat states=Some(global_target_at 28%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 251 states=Some(Gval (Fuint 1) (global_word_28 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 251 (ltac:(reflexivity))).
 have Known := registers 28%nat (ltac:(simpl;tauto)).
 change (VM.find 251 old=Some(Gval (Fuint 1) (global_word_28 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 251 _ generated_module_3_stmts_0 Known initial_register_251); exact Initial.
Qed.
Lemma initial_leaf_29 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 29%nat states=Some(global_target_at 29%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 253 states=Some(Gval (Fuint 1) (global_word_29 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 253 (ltac:(reflexivity))).
 have Known := registers 29%nat (ltac:(simpl;tauto)).
 change (VM.find 253 old=Some(Gval (Fuint 1) (global_word_29 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 253 _ generated_module_3_stmts_0 Known initial_register_253); exact Initial.
Qed.
Lemma initial_leaf_30 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 30%nat states=Some(global_target_at 30%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 255 states=Some(Gval (Fuint 1) (global_word_30 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 255 (ltac:(reflexivity))).
 have Known := registers 30%nat (ltac:(simpl;tauto)).
 change (VM.find 255 old=Some(Gval (Fuint 1) (global_word_30 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 255 _ generated_module_3_stmts_0 Known initial_register_255); exact Initial.
Qed.
Lemma initial_leaf_31 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 31%nat states=Some(global_target_at 31%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 257 states=Some(Gval (Fuint 1) (global_word_31 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 257 (ltac:(reflexivity))).
 have Known := registers 31%nat (ltac:(simpl;tauto)).
 change (VM.find 257 old=Some(Gval (Fuint 1) (global_word_31 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 257 _ generated_module_3_stmts_0 Known initial_register_257); exact Initial.
Qed.
Lemma initial_leaf_32 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 32%nat states=Some(global_target_at 32%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 259 states=Some(Gval (Fuint 1) (global_word_32 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 259 (ltac:(reflexivity))).
 have Known := registers 32%nat (ltac:(simpl;tauto)).
 change (VM.find 259 old=Some(Gval (Fuint 1) (global_word_32 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 259 _ generated_module_3_stmts_0 Known initial_register_259); exact Initial.
Qed.
Lemma initial_leaf_33 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 33%nat states=Some(global_target_at 33%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 261 states=Some(Gval (Fuint 1) (global_word_33 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 261 (ltac:(reflexivity))).
 have Known := registers 33%nat (ltac:(simpl;tauto)).
 change (VM.find 261 old=Some(Gval (Fuint 1) (global_word_33 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 261 _ generated_module_3_stmts_0 Known initial_register_261); exact Initial.
Qed.
Lemma initial_leaf_34 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 34%nat states=Some(global_target_at 34%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 263 states=Some(Gval (Fuint 1) (global_word_34 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 263 (ltac:(reflexivity))).
 have Known := registers 34%nat (ltac:(simpl;tauto)).
 change (VM.find 263 old=Some(Gval (Fuint 1) (global_word_34 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 263 _ generated_module_3_stmts_0 Known initial_register_263); exact Initial.
Qed.
Lemma initial_leaf_35 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 35%nat states=Some(global_target_at 35%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 265 states=Some(Gval (Fuint 1) (global_word_35 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 265 (ltac:(reflexivity))).
 have Known := registers 35%nat (ltac:(simpl;tauto)).
 change (VM.find 265 old=Some(Gval (Fuint 1) (global_word_35 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 265 _ generated_module_3_stmts_0 Known initial_register_265); exact Initial.
Qed.
Lemma initial_leaf_36 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 36%nat states=Some(global_target_at 36%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 267 states=Some(Gval (Fuint 1) (global_word_36 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 267 (ltac:(reflexivity))).
 have Known := registers 36%nat (ltac:(simpl;tauto)).
 change (VM.find 267 old=Some(Gval (Fuint 1) (global_word_36 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 267 _ generated_module_3_stmts_0 Known initial_register_267); exact Initial.
Qed.
Lemma initial_leaf_37 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 37%nat states=Some(global_target_at 37%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 269 states=Some(Gval (Fuint 1) (global_word_37 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 269 (ltac:(reflexivity))).
 have Known := registers 37%nat (ltac:(simpl;tauto)).
 change (VM.find 269 old=Some(Gval (Fuint 1) (global_word_37 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 269 _ generated_module_3_stmts_0 Known initial_register_269); exact Initial.
Qed.
Lemma initial_leaf_38 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 38%nat states=Some(global_target_at 38%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 271 states=Some(Gval (Fuint 1) (global_word_38 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 271 (ltac:(reflexivity))).
 have Known := registers 38%nat (ltac:(simpl;tauto)).
 change (VM.find 271 old=Some(Gval (Fuint 1) (global_word_38 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 271 _ generated_module_3_stmts_0 Known initial_register_271); exact Initial.
Qed.
Lemma initial_leaf_39 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 39%nat states=Some(global_target_at 39%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 273 states=Some(Gval (Fuint 1) (global_word_39 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 273 (ltac:(reflexivity))).
 have Known := registers 39%nat (ltac:(simpl;tauto)).
 change (VM.find 273 old=Some(Gval (Fuint 1) (global_word_39 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 273 _ generated_module_3_stmts_0 Known initial_register_273); exact Initial.
Qed.
Lemma initial_leaf_40 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 40%nat states=Some(global_target_at 40%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 275 states=Some(Gval (Fuint 1) (global_word_40 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 275 (ltac:(reflexivity))).
 have Known := registers 40%nat (ltac:(simpl;tauto)).
 change (VM.find 275 old=Some(Gval (Fuint 1) (global_word_40 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 275 _ generated_module_3_stmts_0 Known initial_register_275); exact Initial.
Qed.
Lemma initial_leaf_41 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 41%nat states=Some(global_target_at 41%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 277 states=Some(Gval (Fuint 1) (global_word_41 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 277 (ltac:(reflexivity))).
 have Known := registers 41%nat (ltac:(simpl;tauto)).
 change (VM.find 277 old=Some(Gval (Fuint 1) (global_word_41 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 277 _ generated_module_3_stmts_0 Known initial_register_277); exact Initial.
Qed.
Lemma initial_leaf_42 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 42%nat states=Some(global_target_at 42%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 279 states=Some(Gval (Fuint 1) (global_word_42 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 279 (ltac:(reflexivity))).
 have Known := registers 42%nat (ltac:(simpl;tauto)).
 change (VM.find 279 old=Some(Gval (Fuint 1) (global_word_42 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 279 _ generated_module_3_stmts_0 Known initial_register_279); exact Initial.
Qed.
Lemma initial_leaf_43 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 43%nat states=Some(global_target_at 43%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 281 states=Some(Gval (Fuint 1) (global_word_43 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 281 (ltac:(reflexivity))).
 have Known := registers 43%nat (ltac:(simpl;tauto)).
 change (VM.find 281 old=Some(Gval (Fuint 1) (global_word_43 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 281 _ generated_module_3_stmts_0 Known initial_register_281); exact Initial.
Qed.
Lemma initial_leaf_44 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 44%nat states=Some(global_target_at 44%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 283 states=Some(Gval (Fuint 1) (global_word_44 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 283 (ltac:(reflexivity))).
 have Known := registers 44%nat (ltac:(simpl;tauto)).
 change (VM.find 283 old=Some(Gval (Fuint 1) (global_word_44 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 283 _ generated_module_3_stmts_0 Known initial_register_283); exact Initial.
Qed.
Lemma initial_leaf_45 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 45%nat states=Some(global_target_at 45%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 285 states=Some(Gval (Fuint 1) (global_word_45 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 285 (ltac:(reflexivity))).
 have Known := registers 45%nat (ltac:(simpl;tauto)).
 change (VM.find 285 old=Some(Gval (Fuint 1) (global_word_45 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 285 _ generated_module_3_stmts_0 Known initial_register_285); exact Initial.
Qed.
Lemma initial_leaf_46 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 46%nat states=Some(global_target_at 46%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 287 states=Some(Gval (Fuint 1) (global_word_46 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 287 (ltac:(reflexivity))).
 have Known := registers 46%nat (ltac:(simpl;tauto)).
 change (VM.find 287 old=Some(Gval (Fuint 1) (global_word_46 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 287 _ generated_module_3_stmts_0 Known initial_register_287); exact Initial.
Qed.
Lemma initial_leaf_47 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 47%nat states=Some(global_target_at 47%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 289 states=Some(Gval (Fuint 1) (global_word_47 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 289 (ltac:(reflexivity))).
 have Known := registers 47%nat (ltac:(simpl;tauto)).
 change (VM.find 289 old=Some(Gval (Fuint 1) (global_word_47 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 289 _ generated_module_3_stmts_0 Known initial_register_289); exact Initial.
Qed.
Lemma initial_leaf_48 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 48%nat states=Some(global_target_at 48%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 291 states=Some(Gval (Fuint 1) (global_word_48 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 291 (ltac:(reflexivity))).
 have Known := registers 48%nat (ltac:(simpl;tauto)).
 change (VM.find 291 old=Some(Gval (Fuint 1) (global_word_48 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 291 _ generated_module_3_stmts_0 Known initial_register_291); exact Initial.
Qed.
Lemma initial_leaf_49 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 49%nat states=Some(global_target_at 49%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 293 states=Some(Gval (Fuint 1) (global_word_49 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 293 (ltac:(reflexivity))).
 have Known := registers 49%nat (ltac:(simpl;tauto)).
 change (VM.find 293 old=Some(Gval (Fuint 1) (global_word_49 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 293 _ generated_module_3_stmts_0 Known initial_register_293); exact Initial.
Qed.
Lemma initial_leaf_50 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 50%nat states=Some(global_target_at 50%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 295 states=Some(Gval (Fuint 1) (global_word_50 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 295 (ltac:(reflexivity))).
 have Known := registers 50%nat (ltac:(simpl;tauto)).
 change (VM.find 295 old=Some(Gval (Fuint 1) (global_word_50 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 295 _ generated_module_3_stmts_0 Known initial_register_295); exact Initial.
Qed.
Lemma initial_leaf_51 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 51%nat states=Some(global_target_at 51%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 297 states=Some(Gval (Fuint 1) (global_word_51 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 297 (ltac:(reflexivity))).
 have Known := registers 51%nat (ltac:(simpl;tauto)).
 change (VM.find 297 old=Some(Gval (Fuint 1) (global_word_51 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 297 _ generated_module_3_stmts_0 Known initial_register_297); exact Initial.
Qed.
Lemma initial_leaf_52 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 52%nat states=Some(global_target_at 52%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 299 states=Some(Gval (Fuint 1) (global_word_52 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 299 (ltac:(reflexivity))).
 have Known := registers 52%nat (ltac:(simpl;tauto)).
 change (VM.find 299 old=Some(Gval (Fuint 1) (global_word_52 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 299 _ generated_module_3_stmts_0 Known initial_register_299); exact Initial.
Qed.
Lemma initial_leaf_53 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 53%nat states=Some(global_target_at 53%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 3 states=Some(Gval (Fuint 8) (global_word_53 v))).
 unfold circuit_lookup. rewrite Found.
 apply multiplier_external_3.
Qed.
Lemma initial_leaf_54 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 54%nat states=Some(global_target_at 54%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 301 states=Some(Gval (Fuint 1) (global_word_54 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 301 (ltac:(reflexivity))).
 have Known := registers 54%nat (ltac:(simpl;tauto)).
 change (VM.find 301 old=Some(Gval (Fuint 1) (global_word_54 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 301 _ generated_module_3_stmts_0 Known initial_register_301); exact Initial.
Qed.
Lemma initial_leaf_55 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 55%nat states=Some(global_target_at 55%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 303 states=Some(Gval (Fuint 1) (global_word_55 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 303 (ltac:(reflexivity))).
 have Known := registers 55%nat (ltac:(simpl;tauto)).
 change (VM.find 303 old=Some(Gval (Fuint 1) (global_word_55 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 303 _ generated_module_3_stmts_0 Known initial_register_303); exact Initial.
Qed.
Lemma initial_leaf_56 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 56%nat states=Some(global_target_at 56%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 4 states=Some(Gval (Fuint 1) (global_word_56 v))).
 unfold circuit_lookup. rewrite Found.
 apply multiplier_external_4.
Qed.
Lemma initial_leaf_57 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 57%nat states=Some(global_target_at 57%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 408 states=Some(Gval (Fuint 16) (global_word_57 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 408 (ltac:(reflexivity))).
 have Known := registers 57%nat (ltac:(simpl;tauto)).
 change (VM.find 408 old=Some(Gval (Fuint 16) (global_word_57 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 408 _ generated_module_3_stmts_0 Known initial_register_408); exact Initial.
Qed.
Lemma initial_leaf_58 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 58%nat states=Some(global_target_at 58%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 410 states=Some(Gval (Fuint 1) (global_word_58 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 410 (ltac:(reflexivity))).
 have Known := registers 58%nat (ltac:(simpl;tauto)).
 change (VM.find 410 old=Some(Gval (Fuint 1) (global_word_58 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 410 _ generated_module_3_stmts_0 Known initial_register_410); exact Initial.
Qed.
Lemma initial_leaf_59 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 59%nat states=Some(global_target_at 59%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 416 states=Some(Gval (Fuint 16) (global_word_59 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 416 (ltac:(reflexivity))).
 have Known := registers 59%nat (ltac:(simpl;tauto)).
 change (VM.find 416 old=Some(Gval (Fuint 16) (global_word_59 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 416 _ generated_module_3_stmts_0 Known initial_register_416); exact Initial.
Qed.
Lemma initial_leaf_60 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 60%nat states=Some(global_target_at 60%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 419 states=Some(Gval (Fuint 1) (global_word_60 v))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 419 (ltac:(reflexivity))).
 have Known := registers 60%nat (ltac:(simpl;tauto)).
 change (VM.find 419 old=Some(Gval (Fuint 1) (global_word_60 v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old 419 _ generated_module_3_stmts_0 Known initial_register_419); exact Initial.
Qed.
Lemma initial_leaf_61 v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at 61%nat states=Some(global_target_at 61%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] 5 states=Some(Gval (Fuint 1) (global_word_61 v))).
 unfold circuit_lookup. rewrite Found.
 apply multiplier_external_5.
Qed.
Lemma rank_zero_is_leaf index (inside:(index<2262)%coq_nat) (zero:(global_rank_at index<=0)%coq_nat) : (index<62)%coq_nat.
Proof.
 have Checked: List.forallb (fun n=>if Nat.leb(global_rank_at n)0 then Nat.ltb n 62 else true)(List.seq 0 2262)=true by vm_compute;reflexivity.
 have Member:List.In index (List.seq 0 2262) by apply List.in_seq;lia.
 have Value := (proj1 (List.forallb_forall _ _) Checked) index Member.
 have Zero:Nat.leb(global_rank_at index)0=true by apply Nat.leb_le;exact zero.
 rewrite Zero in Value. apply Nat.ltb_lt. exact Value.
Qed.
Lemma multiplier_initial_ranked v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_ranked v 0 states.
Proof.
 intros index inside zero. have Bound:=rank_zero_is_leaf index inside zero.
 destruct index as [|index]; [exact(initial_leaf_0 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_1 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_2 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_3 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_4 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_5 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_6 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_7 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_8 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_9 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_10 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_11 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_12 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_13 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_14 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_15 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_16 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_17 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_18 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_19 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_20 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_21 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_22 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_23 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_24 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_25 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_26 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_27 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_28 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_29 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_30 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_31 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_32 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_33 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_34 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_35 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_36 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_37 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_38 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_39 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_40 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_41 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_42 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_43 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_44 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_45 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_46 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_47 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_48 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_49 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_50 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_51 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_52 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_53 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_54 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_55 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_56 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_57 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_58 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_59 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_60 v previous old external states old_found registers ports ran)|].
 destruct index as [|index]; [exact(initial_leaf_61 v previous old external states old_found registers ports ran)|].
 lia.
Qed.
