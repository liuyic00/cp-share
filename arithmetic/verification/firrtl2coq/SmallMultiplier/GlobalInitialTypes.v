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
Lemma initial_type_278 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 278%nat states)=Some(Gtyp(global_type_at 278%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 7 2 states)=Some(Gtyp(global_type_at 278%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 7 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_7 _ env Initial). reflexivity.
Qed.
Lemma initial_type_281 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 281%nat states)=Some(Gtyp(global_type_at 281%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 7 3 states)=Some(Gtyp(global_type_at 281%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 7 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_7 _ env Initial). reflexivity.
Qed.
Lemma initial_type_289 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 289%nat states)=Some(Gtyp(global_type_at 289%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::7] 0 (multiplier_ports 0) generated_module_0_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::7] 4 states)=Some(Gtyp(global_type_at 289%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_0_4 _ env Initial). reflexivity.
Qed.
Lemma initial_type_293 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 293%nat states)=Some(Gtyp(global_type_at 293%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::7] 0 (multiplier_ports 0) generated_module_0_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::7] 5 states)=Some(Gtyp(global_type_at 293%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_0_5 _ env Initial). reflexivity.
Qed.
Lemma initial_type_296 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 296%nat states)=Some(Gtyp(global_type_at 296%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 8 2 states)=Some(Gtyp(global_type_at 296%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 8 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_8 _ env Initial). reflexivity.
Qed.
Lemma initial_type_299 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 299%nat states)=Some(Gtyp(global_type_at 299%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 8 3 states)=Some(Gtyp(global_type_at 299%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 8 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_8 _ env Initial). reflexivity.
Qed.
Lemma initial_type_307 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 307%nat states)=Some(Gtyp(global_type_at 307%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::8] 0 (multiplier_ports 0) generated_module_0_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::8] 4 states)=Some(Gtyp(global_type_at 307%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_0_4 _ env Initial). reflexivity.
Qed.
Lemma initial_type_311 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 311%nat states)=Some(Gtyp(global_type_at 311%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::8] 0 (multiplier_ports 0) generated_module_0_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::8] 5 states)=Some(Gtyp(global_type_at 311%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_0_5 _ env Initial). reflexivity.
Qed.
Lemma initial_type_314 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 314%nat states)=Some(Gtyp(global_type_at 314%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 9 4 states)=Some(Gtyp(global_type_at 314%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 9 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_9 _ env Initial). reflexivity.
Qed.
Lemma initial_type_317 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 317%nat states)=Some(Gtyp(global_type_at 317%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 9 2 states)=Some(Gtyp(global_type_at 317%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 9 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_9 _ env Initial). reflexivity.
Qed.
Lemma initial_type_320 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 320%nat states)=Some(Gtyp(global_type_at 320%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 9 3 states)=Some(Gtyp(global_type_at 320%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 9 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_9 _ env Initial). reflexivity.
Qed.
Lemma initial_type_331 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 331%nat states)=Some(Gtyp(global_type_at 331%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::9] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::9] 5 states)=Some(Gtyp(global_type_at 331%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_5 _ env Initial). reflexivity.
Qed.
Lemma initial_type_335 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 335%nat states)=Some(Gtyp(global_type_at 335%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::9] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::9] 6 states)=Some(Gtyp(global_type_at 335%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_6 _ env Initial). reflexivity.
Qed.
Lemma initial_type_338 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 338%nat states)=Some(Gtyp(global_type_at 338%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 10 4 states)=Some(Gtyp(global_type_at 338%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 10 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_341 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 341%nat states)=Some(Gtyp(global_type_at 341%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 10 2 states)=Some(Gtyp(global_type_at 341%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 10 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_344 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 344%nat states)=Some(Gtyp(global_type_at 344%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 10 3 states)=Some(Gtyp(global_type_at 344%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 10 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_355 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 355%nat states)=Some(Gtyp(global_type_at 355%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::10] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::10] 5 states)=Some(Gtyp(global_type_at 355%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_5 _ env Initial). reflexivity.
Qed.
Lemma initial_type_359 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 359%nat states)=Some(Gtyp(global_type_at 359%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::10] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::10] 6 states)=Some(Gtyp(global_type_at 359%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_6 _ env Initial). reflexivity.
Qed.
Lemma initial_type_362 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 362%nat states)=Some(Gtyp(global_type_at 362%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 11 6 states)=Some(Gtyp(global_type_at 362%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 11 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_365 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 365%nat states)=Some(Gtyp(global_type_at 365%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::11] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::11] 11 4 states)=Some(Gtyp(global_type_at 365%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_368 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 368%nat states)=Some(Gtyp(global_type_at 368%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 11 4 states)=Some(Gtyp(global_type_at 368%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 11 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_370 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 370%nat states)=Some(Gtyp(global_type_at 370%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::11] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::11] 10 4 states)=Some(Gtyp(global_type_at 370%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_373 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 373%nat states)=Some(Gtyp(global_type_at 373%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 11 2 states)=Some(Gtyp(global_type_at 373%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 11 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_375 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 375%nat states)=Some(Gtyp(global_type_at 375%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::11] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::11] 10 2 states)=Some(Gtyp(global_type_at 375%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_378 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 378%nat states)=Some(Gtyp(global_type_at 378%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 11 3 states)=Some(Gtyp(global_type_at 378%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 11 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_380 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 380%nat states)=Some(Gtyp(global_type_at 380%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::11] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::11] 10 3 states)=Some(Gtyp(global_type_at 380%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_391 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 391%nat states)=Some(Gtyp(global_type_at 391%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::10;11] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::10;11] 5 states)=Some(Gtyp(global_type_at 391%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_5 _ env Initial). reflexivity.
Qed.
Lemma initial_type_394 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 394%nat states)=Some(Gtyp(global_type_at 394%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::11] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::11] 11 2 states)=Some(Gtyp(global_type_at 394%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_397 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 397%nat states)=Some(Gtyp(global_type_at 397%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 11 5 states)=Some(Gtyp(global_type_at 397%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 11 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_400 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 400%nat states)=Some(Gtyp(global_type_at 400%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::11] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::11] 11 3 states)=Some(Gtyp(global_type_at 400%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_411 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 411%nat states)=Some(Gtyp(global_type_at 411%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::11;11] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::11;11] 5 states)=Some(Gtyp(global_type_at 411%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_5 _ env Initial). reflexivity.
Qed.
Lemma initial_type_414 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 414%nat states)=Some(Gtyp(global_type_at 414%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::11] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::11] 7 states)=Some(Gtyp(global_type_at 414%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_2_7 _ env Initial). reflexivity.
Qed.
Lemma initial_type_418 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 418%nat states)=Some(Gtyp(global_type_at 418%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::10;11] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::10;11] 6 states)=Some(Gtyp(global_type_at 418%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_6 _ env Initial). reflexivity.
Qed.
Lemma initial_type_421 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 421%nat states)=Some(Gtyp(global_type_at 421%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::11] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::11] 8 states)=Some(Gtyp(global_type_at 421%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_2_8 _ env Initial). reflexivity.
Qed.
Lemma initial_type_425 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 425%nat states)=Some(Gtyp(global_type_at 425%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::11;11] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::11;11] 6 states)=Some(Gtyp(global_type_at 425%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_6 _ env Initial). reflexivity.
Qed.
Lemma initial_type_428 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 428%nat states)=Some(Gtyp(global_type_at 428%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::11] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::11] 9 states)=Some(Gtyp(global_type_at 428%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_2_9 _ env Initial). reflexivity.
Qed.
Lemma initial_type_431 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 431%nat states)=Some(Gtyp(global_type_at 431%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 12 6 states)=Some(Gtyp(global_type_at 431%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 12 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_12 _ env Initial). reflexivity.
Qed.
Lemma initial_type_434 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 434%nat states)=Some(Gtyp(global_type_at 434%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::12] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::12] 11 4 states)=Some(Gtyp(global_type_at 434%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_437 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 437%nat states)=Some(Gtyp(global_type_at 437%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 12 4 states)=Some(Gtyp(global_type_at 437%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 12 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_12 _ env Initial). reflexivity.
Qed.
Lemma initial_type_439 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 439%nat states)=Some(Gtyp(global_type_at 439%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::12] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::12] 10 4 states)=Some(Gtyp(global_type_at 439%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_442 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 442%nat states)=Some(Gtyp(global_type_at 442%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 12 2 states)=Some(Gtyp(global_type_at 442%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 12 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_12 _ env Initial). reflexivity.
Qed.
Lemma initial_type_444 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 444%nat states)=Some(Gtyp(global_type_at 444%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::12] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::12] 10 2 states)=Some(Gtyp(global_type_at 444%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_447 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 447%nat states)=Some(Gtyp(global_type_at 447%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 12 3 states)=Some(Gtyp(global_type_at 447%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 12 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_12 _ env Initial). reflexivity.
Qed.
Lemma initial_type_449 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 449%nat states)=Some(Gtyp(global_type_at 449%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::12] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::12] 10 3 states)=Some(Gtyp(global_type_at 449%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_460 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 460%nat states)=Some(Gtyp(global_type_at 460%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::10;12] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::10;12] 5 states)=Some(Gtyp(global_type_at 460%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_5 _ env Initial). reflexivity.
Qed.
Lemma initial_type_463 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 463%nat states)=Some(Gtyp(global_type_at 463%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::12] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::12] 11 2 states)=Some(Gtyp(global_type_at 463%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_466 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 466%nat states)=Some(Gtyp(global_type_at 466%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 12 5 states)=Some(Gtyp(global_type_at 466%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 12 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_12 _ env Initial). reflexivity.
Qed.
Lemma initial_type_469 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 469%nat states)=Some(Gtyp(global_type_at 469%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::12] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::12] 11 3 states)=Some(Gtyp(global_type_at 469%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_480 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 480%nat states)=Some(Gtyp(global_type_at 480%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::11;12] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::11;12] 5 states)=Some(Gtyp(global_type_at 480%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_5 _ env Initial). reflexivity.
Qed.
Lemma initial_type_483 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 483%nat states)=Some(Gtyp(global_type_at 483%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::12] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::12] 7 states)=Some(Gtyp(global_type_at 483%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_2_7 _ env Initial). reflexivity.
Qed.
Lemma initial_type_487 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 487%nat states)=Some(Gtyp(global_type_at 487%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::10;12] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::10;12] 6 states)=Some(Gtyp(global_type_at 487%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_6 _ env Initial). reflexivity.
Qed.
Lemma initial_type_490 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 490%nat states)=Some(Gtyp(global_type_at 490%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::12] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::12] 8 states)=Some(Gtyp(global_type_at 490%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_2_8 _ env Initial). reflexivity.
Qed.
Lemma initial_type_494 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 494%nat states)=Some(Gtyp(global_type_at 494%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::11;12] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::11;12] 6 states)=Some(Gtyp(global_type_at 494%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_6 _ env Initial). reflexivity.
Qed.
Lemma initial_type_497 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 497%nat states)=Some(Gtyp(global_type_at 497%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::12] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::12] 9 states)=Some(Gtyp(global_type_at 497%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_2_9 _ env Initial). reflexivity.
Qed.
Lemma initial_type_500 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 500%nat states)=Some(Gtyp(global_type_at 500%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 13 6 states)=Some(Gtyp(global_type_at 500%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 13 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_13 _ env Initial). reflexivity.
Qed.
Lemma initial_type_503 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 503%nat states)=Some(Gtyp(global_type_at 503%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::13] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::13] 11 4 states)=Some(Gtyp(global_type_at 503%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_506 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 506%nat states)=Some(Gtyp(global_type_at 506%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 13 4 states)=Some(Gtyp(global_type_at 506%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 13 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_13 _ env Initial). reflexivity.
Qed.
Lemma initial_type_508 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 508%nat states)=Some(Gtyp(global_type_at 508%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::13] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::13] 10 4 states)=Some(Gtyp(global_type_at 508%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_511 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 511%nat states)=Some(Gtyp(global_type_at 511%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 13 2 states)=Some(Gtyp(global_type_at 511%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 13 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_13 _ env Initial). reflexivity.
Qed.
Lemma initial_type_513 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 513%nat states)=Some(Gtyp(global_type_at 513%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::13] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::13] 10 2 states)=Some(Gtyp(global_type_at 513%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_516 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 516%nat states)=Some(Gtyp(global_type_at 516%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 13 3 states)=Some(Gtyp(global_type_at 516%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 13 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_13 _ env Initial). reflexivity.
Qed.
Lemma initial_type_518 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 518%nat states)=Some(Gtyp(global_type_at 518%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::13] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::13] 10 3 states)=Some(Gtyp(global_type_at 518%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_529 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 529%nat states)=Some(Gtyp(global_type_at 529%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::10;13] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::10;13] 5 states)=Some(Gtyp(global_type_at 529%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_5 _ env Initial). reflexivity.
Qed.
Lemma initial_type_532 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 532%nat states)=Some(Gtyp(global_type_at 532%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::13] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::13] 11 2 states)=Some(Gtyp(global_type_at 532%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_535 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 535%nat states)=Some(Gtyp(global_type_at 535%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 13 5 states)=Some(Gtyp(global_type_at 535%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 13 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_13 _ env Initial). reflexivity.
Qed.
Lemma initial_type_538 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 538%nat states)=Some(Gtyp(global_type_at 538%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::13] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::13] 11 3 states)=Some(Gtyp(global_type_at 538%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_549 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 549%nat states)=Some(Gtyp(global_type_at 549%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::11;13] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::11;13] 5 states)=Some(Gtyp(global_type_at 549%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_5 _ env Initial). reflexivity.
Qed.
Lemma initial_type_552 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 552%nat states)=Some(Gtyp(global_type_at 552%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::13] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::13] 7 states)=Some(Gtyp(global_type_at 552%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_2_7 _ env Initial). reflexivity.
Qed.
Lemma initial_type_556 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 556%nat states)=Some(Gtyp(global_type_at 556%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::10;13] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::10;13] 6 states)=Some(Gtyp(global_type_at 556%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_6 _ env Initial). reflexivity.
Qed.
Lemma initial_type_559 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 559%nat states)=Some(Gtyp(global_type_at 559%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::13] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::13] 8 states)=Some(Gtyp(global_type_at 559%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_2_8 _ env Initial). reflexivity.
Qed.
Lemma initial_type_563 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 563%nat states)=Some(Gtyp(global_type_at 563%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::11;13] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::11;13] 6 states)=Some(Gtyp(global_type_at 563%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_6 _ env Initial). reflexivity.
Qed.
Lemma initial_type_566 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 566%nat states)=Some(Gtyp(global_type_at 566%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::13] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::13] 9 states)=Some(Gtyp(global_type_at 566%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_2_9 _ env Initial). reflexivity.
Qed.
Lemma initial_type_569 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 569%nat states)=Some(Gtyp(global_type_at 569%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 14 6 states)=Some(Gtyp(global_type_at 569%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 14 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_14 _ env Initial). reflexivity.
Qed.
Lemma initial_type_572 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 572%nat states)=Some(Gtyp(global_type_at 572%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::14] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::14] 11 4 states)=Some(Gtyp(global_type_at 572%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_575 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 575%nat states)=Some(Gtyp(global_type_at 575%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 14 4 states)=Some(Gtyp(global_type_at 575%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 14 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_14 _ env Initial). reflexivity.
Qed.
Lemma initial_type_577 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 577%nat states)=Some(Gtyp(global_type_at 577%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::14] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::14] 10 4 states)=Some(Gtyp(global_type_at 577%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_580 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 580%nat states)=Some(Gtyp(global_type_at 580%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 14 2 states)=Some(Gtyp(global_type_at 580%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 14 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_14 _ env Initial). reflexivity.
Qed.
Lemma initial_type_582 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 582%nat states)=Some(Gtyp(global_type_at 582%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::14] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::14] 10 2 states)=Some(Gtyp(global_type_at 582%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_585 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 585%nat states)=Some(Gtyp(global_type_at 585%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 14 3 states)=Some(Gtyp(global_type_at 585%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 14 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_14 _ env Initial). reflexivity.
Qed.
Lemma initial_type_587 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 587%nat states)=Some(Gtyp(global_type_at 587%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::14] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::14] 10 3 states)=Some(Gtyp(global_type_at 587%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_598 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 598%nat states)=Some(Gtyp(global_type_at 598%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::10;14] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::10;14] 5 states)=Some(Gtyp(global_type_at 598%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_5 _ env Initial). reflexivity.
Qed.
Lemma initial_type_601 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 601%nat states)=Some(Gtyp(global_type_at 601%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::14] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::14] 11 2 states)=Some(Gtyp(global_type_at 601%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_604 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 604%nat states)=Some(Gtyp(global_type_at 604%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 14 5 states)=Some(Gtyp(global_type_at 604%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 14 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_14 _ env Initial). reflexivity.
Qed.
Lemma initial_type_607 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 607%nat states)=Some(Gtyp(global_type_at 607%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::14] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::14] 11 3 states)=Some(Gtyp(global_type_at 607%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_618 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 618%nat states)=Some(Gtyp(global_type_at 618%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::11;14] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::11;14] 5 states)=Some(Gtyp(global_type_at 618%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_5 _ env Initial). reflexivity.
Qed.
Lemma initial_type_621 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 621%nat states)=Some(Gtyp(global_type_at 621%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::14] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::14] 7 states)=Some(Gtyp(global_type_at 621%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_2_7 _ env Initial). reflexivity.
Qed.
Lemma initial_type_625 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 625%nat states)=Some(Gtyp(global_type_at 625%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::10;14] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::10;14] 6 states)=Some(Gtyp(global_type_at 625%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_6 _ env Initial). reflexivity.
Qed.
Lemma initial_type_628 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 628%nat states)=Some(Gtyp(global_type_at 628%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::14] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::14] 8 states)=Some(Gtyp(global_type_at 628%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_2_8 _ env Initial). reflexivity.
Qed.
Lemma initial_type_632 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 632%nat states)=Some(Gtyp(global_type_at 632%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::11;14] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::11;14] 6 states)=Some(Gtyp(global_type_at 632%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_6 _ env Initial). reflexivity.
Qed.
Lemma initial_type_635 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 635%nat states)=Some(Gtyp(global_type_at 635%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::14] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::14] 9 states)=Some(Gtyp(global_type_at 635%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_2_9 _ env Initial). reflexivity.
Qed.
Lemma initial_type_638 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 638%nat states)=Some(Gtyp(global_type_at 638%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 15 6 states)=Some(Gtyp(global_type_at 638%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 15 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_15 _ env Initial). reflexivity.
Qed.
Lemma initial_type_641 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 641%nat states)=Some(Gtyp(global_type_at 641%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::15] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::15] 11 4 states)=Some(Gtyp(global_type_at 641%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_644 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 644%nat states)=Some(Gtyp(global_type_at 644%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 15 4 states)=Some(Gtyp(global_type_at 644%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 15 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_15 _ env Initial). reflexivity.
Qed.
Lemma initial_type_646 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 646%nat states)=Some(Gtyp(global_type_at 646%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::15] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::15] 10 4 states)=Some(Gtyp(global_type_at 646%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_649 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 649%nat states)=Some(Gtyp(global_type_at 649%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 15 2 states)=Some(Gtyp(global_type_at 649%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 15 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_15 _ env Initial). reflexivity.
Qed.
Lemma initial_type_651 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 651%nat states)=Some(Gtyp(global_type_at 651%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::15] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::15] 10 2 states)=Some(Gtyp(global_type_at 651%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_654 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 654%nat states)=Some(Gtyp(global_type_at 654%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 15 3 states)=Some(Gtyp(global_type_at 654%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 15 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_15 _ env Initial). reflexivity.
Qed.
Lemma initial_type_656 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 656%nat states)=Some(Gtyp(global_type_at 656%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::15] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::15] 10 3 states)=Some(Gtyp(global_type_at 656%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_667 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 667%nat states)=Some(Gtyp(global_type_at 667%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::10;15] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::10;15] 5 states)=Some(Gtyp(global_type_at 667%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_5 _ env Initial). reflexivity.
Qed.
Lemma initial_type_670 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 670%nat states)=Some(Gtyp(global_type_at 670%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::15] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::15] 11 2 states)=Some(Gtyp(global_type_at 670%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_673 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 673%nat states)=Some(Gtyp(global_type_at 673%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 15 5 states)=Some(Gtyp(global_type_at 673%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 15 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_15 _ env Initial). reflexivity.
Qed.
Lemma initial_type_676 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 676%nat states)=Some(Gtyp(global_type_at 676%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::15] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::15] 11 3 states)=Some(Gtyp(global_type_at 676%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_687 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 687%nat states)=Some(Gtyp(global_type_at 687%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::11;15] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::11;15] 5 states)=Some(Gtyp(global_type_at 687%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_5 _ env Initial). reflexivity.
Qed.
Lemma initial_type_690 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 690%nat states)=Some(Gtyp(global_type_at 690%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::15] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::15] 7 states)=Some(Gtyp(global_type_at 690%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_2_7 _ env Initial). reflexivity.
Qed.
Lemma initial_type_694 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 694%nat states)=Some(Gtyp(global_type_at 694%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::10;15] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::10;15] 6 states)=Some(Gtyp(global_type_at 694%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_6 _ env Initial). reflexivity.
Qed.
Lemma initial_type_697 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 697%nat states)=Some(Gtyp(global_type_at 697%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::15] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::15] 8 states)=Some(Gtyp(global_type_at 697%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_2_8 _ env Initial). reflexivity.
Qed.
Lemma initial_type_701 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 701%nat states)=Some(Gtyp(global_type_at 701%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::11;15] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::11;15] 6 states)=Some(Gtyp(global_type_at 701%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_6 _ env Initial). reflexivity.
Qed.
Lemma initial_type_704 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 704%nat states)=Some(Gtyp(global_type_at 704%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::15] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::15] 9 states)=Some(Gtyp(global_type_at 704%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_2_9 _ env Initial). reflexivity.
Qed.
Lemma initial_type_707 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 707%nat states)=Some(Gtyp(global_type_at 707%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 16 6 states)=Some(Gtyp(global_type_at 707%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 16 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_16 _ env Initial). reflexivity.
Qed.
Lemma initial_type_710 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 710%nat states)=Some(Gtyp(global_type_at 710%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::16] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::16] 11 4 states)=Some(Gtyp(global_type_at 710%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_713 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 713%nat states)=Some(Gtyp(global_type_at 713%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 16 4 states)=Some(Gtyp(global_type_at 713%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 16 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_16 _ env Initial). reflexivity.
Qed.
Lemma initial_type_715 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 715%nat states)=Some(Gtyp(global_type_at 715%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::16] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::16] 10 4 states)=Some(Gtyp(global_type_at 715%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_718 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 718%nat states)=Some(Gtyp(global_type_at 718%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 16 2 states)=Some(Gtyp(global_type_at 718%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 16 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_16 _ env Initial). reflexivity.
Qed.
Lemma initial_type_720 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 720%nat states)=Some(Gtyp(global_type_at 720%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::16] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::16] 10 2 states)=Some(Gtyp(global_type_at 720%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_723 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 723%nat states)=Some(Gtyp(global_type_at 723%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 16 3 states)=Some(Gtyp(global_type_at 723%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 16 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_16 _ env Initial). reflexivity.
Qed.
Lemma initial_type_725 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 725%nat states)=Some(Gtyp(global_type_at 725%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::16] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::16] 10 3 states)=Some(Gtyp(global_type_at 725%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_736 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 736%nat states)=Some(Gtyp(global_type_at 736%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::10;16] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::10;16] 5 states)=Some(Gtyp(global_type_at 736%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_5 _ env Initial). reflexivity.
Qed.
Lemma initial_type_739 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 739%nat states)=Some(Gtyp(global_type_at 739%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::16] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::16] 11 2 states)=Some(Gtyp(global_type_at 739%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_742 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 742%nat states)=Some(Gtyp(global_type_at 742%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 16 5 states)=Some(Gtyp(global_type_at 742%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 16 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_16 _ env Initial). reflexivity.
Qed.
Lemma initial_type_745 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 745%nat states)=Some(Gtyp(global_type_at 745%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::16] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::16] 11 3 states)=Some(Gtyp(global_type_at 745%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_756 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 756%nat states)=Some(Gtyp(global_type_at 756%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::11;16] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::11;16] 5 states)=Some(Gtyp(global_type_at 756%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_5 _ env Initial). reflexivity.
Qed.
Lemma initial_type_759 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 759%nat states)=Some(Gtyp(global_type_at 759%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::16] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::16] 7 states)=Some(Gtyp(global_type_at 759%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_2_7 _ env Initial). reflexivity.
Qed.
Lemma initial_type_763 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 763%nat states)=Some(Gtyp(global_type_at 763%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::10;16] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::10;16] 6 states)=Some(Gtyp(global_type_at 763%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_6 _ env Initial). reflexivity.
Qed.
Lemma initial_type_766 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 766%nat states)=Some(Gtyp(global_type_at 766%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::16] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::16] 8 states)=Some(Gtyp(global_type_at 766%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_2_8 _ env Initial). reflexivity.
Qed.
Lemma initial_type_770 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 770%nat states)=Some(Gtyp(global_type_at 770%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::11;16] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::11;16] 6 states)=Some(Gtyp(global_type_at 770%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_6 _ env Initial). reflexivity.
Qed.
Lemma initial_type_773 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 773%nat states)=Some(Gtyp(global_type_at 773%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::16] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::16] 9 states)=Some(Gtyp(global_type_at 773%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_2_9 _ env Initial). reflexivity.
Qed.
Lemma initial_type_776 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 776%nat states)=Some(Gtyp(global_type_at 776%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 17 6 states)=Some(Gtyp(global_type_at 776%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 17 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_17 _ env Initial). reflexivity.
Qed.
Lemma initial_type_779 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 779%nat states)=Some(Gtyp(global_type_at 779%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::17] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::17] 11 4 states)=Some(Gtyp(global_type_at 779%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_782 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 782%nat states)=Some(Gtyp(global_type_at 782%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 17 4 states)=Some(Gtyp(global_type_at 782%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 17 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_17 _ env Initial). reflexivity.
Qed.
Lemma initial_type_784 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 784%nat states)=Some(Gtyp(global_type_at 784%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::17] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::17] 10 4 states)=Some(Gtyp(global_type_at 784%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_787 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 787%nat states)=Some(Gtyp(global_type_at 787%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 17 2 states)=Some(Gtyp(global_type_at 787%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 17 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_17 _ env Initial). reflexivity.
Qed.
Lemma initial_type_789 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 789%nat states)=Some(Gtyp(global_type_at 789%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::17] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::17] 10 2 states)=Some(Gtyp(global_type_at 789%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_792 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 792%nat states)=Some(Gtyp(global_type_at 792%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 17 3 states)=Some(Gtyp(global_type_at 792%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 17 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_17 _ env Initial). reflexivity.
Qed.
Lemma initial_type_794 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 794%nat states)=Some(Gtyp(global_type_at 794%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::17] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::17] 10 3 states)=Some(Gtyp(global_type_at 794%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_805 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 805%nat states)=Some(Gtyp(global_type_at 805%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::10;17] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::10;17] 5 states)=Some(Gtyp(global_type_at 805%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_5 _ env Initial). reflexivity.
Qed.
Lemma initial_type_808 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 808%nat states)=Some(Gtyp(global_type_at 808%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::17] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::17] 11 2 states)=Some(Gtyp(global_type_at 808%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_811 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 811%nat states)=Some(Gtyp(global_type_at 811%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 17 5 states)=Some(Gtyp(global_type_at 811%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 17 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_17 _ env Initial). reflexivity.
Qed.
Lemma initial_type_814 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 814%nat states)=Some(Gtyp(global_type_at 814%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::17] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::17] 11 3 states)=Some(Gtyp(global_type_at 814%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_825 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 825%nat states)=Some(Gtyp(global_type_at 825%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::11;17] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::11;17] 5 states)=Some(Gtyp(global_type_at 825%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_5 _ env Initial). reflexivity.
Qed.
Lemma initial_type_828 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 828%nat states)=Some(Gtyp(global_type_at 828%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::17] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::17] 7 states)=Some(Gtyp(global_type_at 828%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_2_7 _ env Initial). reflexivity.
Qed.
Lemma initial_type_832 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 832%nat states)=Some(Gtyp(global_type_at 832%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::10;17] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::10;17] 6 states)=Some(Gtyp(global_type_at 832%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_6 _ env Initial). reflexivity.
Qed.
Lemma initial_type_835 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 835%nat states)=Some(Gtyp(global_type_at 835%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::17] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::17] 8 states)=Some(Gtyp(global_type_at 835%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_2_8 _ env Initial). reflexivity.
Qed.
Lemma initial_type_839 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 839%nat states)=Some(Gtyp(global_type_at 839%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::11;17] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::11;17] 6 states)=Some(Gtyp(global_type_at 839%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_6 _ env Initial). reflexivity.
Qed.
Lemma initial_type_842 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 842%nat states)=Some(Gtyp(global_type_at 842%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::17] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::17] 9 states)=Some(Gtyp(global_type_at 842%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_2_9 _ env Initial). reflexivity.
Qed.
Lemma initial_type_845 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 845%nat states)=Some(Gtyp(global_type_at 845%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 18 6 states)=Some(Gtyp(global_type_at 845%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 18 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_18 _ env Initial). reflexivity.
Qed.
Lemma initial_type_848 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 848%nat states)=Some(Gtyp(global_type_at 848%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::18] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::18] 11 4 states)=Some(Gtyp(global_type_at 848%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_851 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 851%nat states)=Some(Gtyp(global_type_at 851%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 18 4 states)=Some(Gtyp(global_type_at 851%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 18 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_18 _ env Initial). reflexivity.
Qed.
Lemma initial_type_853 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 853%nat states)=Some(Gtyp(global_type_at 853%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::18] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::18] 10 4 states)=Some(Gtyp(global_type_at 853%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_856 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 856%nat states)=Some(Gtyp(global_type_at 856%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 18 2 states)=Some(Gtyp(global_type_at 856%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 18 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_18 _ env Initial). reflexivity.
Qed.
Lemma initial_type_858 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 858%nat states)=Some(Gtyp(global_type_at 858%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::18] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::18] 10 2 states)=Some(Gtyp(global_type_at 858%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_861 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 861%nat states)=Some(Gtyp(global_type_at 861%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 18 3 states)=Some(Gtyp(global_type_at 861%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 18 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_18 _ env Initial). reflexivity.
Qed.
Lemma initial_type_863 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 863%nat states)=Some(Gtyp(global_type_at 863%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::18] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::18] 10 3 states)=Some(Gtyp(global_type_at 863%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_874 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 874%nat states)=Some(Gtyp(global_type_at 874%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::10;18] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::10;18] 5 states)=Some(Gtyp(global_type_at 874%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_5 _ env Initial). reflexivity.
Qed.
Lemma initial_type_877 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 877%nat states)=Some(Gtyp(global_type_at 877%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::18] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::18] 11 2 states)=Some(Gtyp(global_type_at 877%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_880 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 880%nat states)=Some(Gtyp(global_type_at 880%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 18 5 states)=Some(Gtyp(global_type_at 880%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 18 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_18 _ env Initial). reflexivity.
Qed.
Lemma initial_type_883 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 883%nat states)=Some(Gtyp(global_type_at 883%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::18] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::18] 11 3 states)=Some(Gtyp(global_type_at 883%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_894 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 894%nat states)=Some(Gtyp(global_type_at 894%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::11;18] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::11;18] 5 states)=Some(Gtyp(global_type_at 894%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_5 _ env Initial). reflexivity.
Qed.
Lemma initial_type_897 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 897%nat states)=Some(Gtyp(global_type_at 897%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::18] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::18] 7 states)=Some(Gtyp(global_type_at 897%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_2_7 _ env Initial). reflexivity.
Qed.
Lemma initial_type_901 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 901%nat states)=Some(Gtyp(global_type_at 901%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::10;18] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::10;18] 6 states)=Some(Gtyp(global_type_at 901%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_6 _ env Initial). reflexivity.
Qed.
Lemma initial_type_904 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 904%nat states)=Some(Gtyp(global_type_at 904%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::18] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::18] 8 states)=Some(Gtyp(global_type_at 904%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_2_8 _ env Initial). reflexivity.
Qed.
Lemma initial_type_908 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 908%nat states)=Some(Gtyp(global_type_at 908%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::11;18] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::11;18] 6 states)=Some(Gtyp(global_type_at 908%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_6 _ env Initial). reflexivity.
Qed.
Lemma initial_type_911 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 911%nat states)=Some(Gtyp(global_type_at 911%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::18] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::18] 9 states)=Some(Gtyp(global_type_at 911%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_2_9 _ env Initial). reflexivity.
Qed.
Lemma initial_type_914 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 914%nat states)=Some(Gtyp(global_type_at 914%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 19 4 states)=Some(Gtyp(global_type_at 914%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 19 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_19 _ env Initial). reflexivity.
Qed.
Lemma initial_type_917 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 917%nat states)=Some(Gtyp(global_type_at 917%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 19 2 states)=Some(Gtyp(global_type_at 917%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 19 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_19 _ env Initial). reflexivity.
Qed.
Lemma initial_type_920 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 920%nat states)=Some(Gtyp(global_type_at 920%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 19 3 states)=Some(Gtyp(global_type_at 920%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 19 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_19 _ env Initial). reflexivity.
Qed.
Lemma initial_type_931 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 931%nat states)=Some(Gtyp(global_type_at 931%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::19] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::19] 5 states)=Some(Gtyp(global_type_at 931%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_5 _ env Initial). reflexivity.
Qed.
Lemma initial_type_935 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 935%nat states)=Some(Gtyp(global_type_at 935%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::19] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::19] 6 states)=Some(Gtyp(global_type_at 935%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_6 _ env Initial). reflexivity.
Qed.
Lemma initial_type_938 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 938%nat states)=Some(Gtyp(global_type_at 938%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 20 2 states)=Some(Gtyp(global_type_at 938%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 20 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_20 _ env Initial). reflexivity.
Qed.
Lemma initial_type_941 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 941%nat states)=Some(Gtyp(global_type_at 941%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 20 3 states)=Some(Gtyp(global_type_at 941%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 20 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_20 _ env Initial). reflexivity.
Qed.
Lemma initial_type_949 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 949%nat states)=Some(Gtyp(global_type_at 949%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::20] 0 (multiplier_ports 0) generated_module_0_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::20] 4 states)=Some(Gtyp(global_type_at 949%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_0_4 _ env Initial). reflexivity.
Qed.
Lemma initial_type_953 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 953%nat states)=Some(Gtyp(global_type_at 953%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::20] 0 (multiplier_ports 0) generated_module_0_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::20] 5 states)=Some(Gtyp(global_type_at 953%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_0_5 _ env Initial). reflexivity.
Qed.
Lemma initial_type_956 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 956%nat states)=Some(Gtyp(global_type_at 956%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 21 2 states)=Some(Gtyp(global_type_at 956%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 21 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_21 _ env Initial). reflexivity.
Qed.
Lemma initial_type_959 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 959%nat states)=Some(Gtyp(global_type_at 959%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 21 3 states)=Some(Gtyp(global_type_at 959%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 21 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_21 _ env Initial). reflexivity.
Qed.
Lemma initial_type_967 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 967%nat states)=Some(Gtyp(global_type_at 967%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::21] 0 (multiplier_ports 0) generated_module_0_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::21] 4 states)=Some(Gtyp(global_type_at 967%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_0_4 _ env Initial). reflexivity.
Qed.
Lemma initial_type_971 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 971%nat states)=Some(Gtyp(global_type_at 971%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::21] 0 (multiplier_ports 0) generated_module_0_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::21] 5 states)=Some(Gtyp(global_type_at 971%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_0_5 _ env Initial). reflexivity.
Qed.
Lemma initial_type_974 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 974%nat states)=Some(Gtyp(global_type_at 974%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 22 2 states)=Some(Gtyp(global_type_at 974%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 22 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_22 _ env Initial). reflexivity.
Qed.
Lemma initial_type_977 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 977%nat states)=Some(Gtyp(global_type_at 977%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 22 3 states)=Some(Gtyp(global_type_at 977%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 22 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_22 _ env Initial). reflexivity.
Qed.
Lemma initial_type_985 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 985%nat states)=Some(Gtyp(global_type_at 985%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::22] 0 (multiplier_ports 0) generated_module_0_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::22] 4 states)=Some(Gtyp(global_type_at 985%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_0_4 _ env Initial). reflexivity.
Qed.
Lemma initial_type_989 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 989%nat states)=Some(Gtyp(global_type_at 989%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::22] 0 (multiplier_ports 0) generated_module_0_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::22] 5 states)=Some(Gtyp(global_type_at 989%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_0_5 _ env Initial). reflexivity.
Qed.
Lemma initial_type_992 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 992%nat states)=Some(Gtyp(global_type_at 992%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 23 2 states)=Some(Gtyp(global_type_at 992%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 23 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_23 _ env Initial). reflexivity.
Qed.
Lemma initial_type_995 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 995%nat states)=Some(Gtyp(global_type_at 995%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 23 3 states)=Some(Gtyp(global_type_at 995%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 23 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_23 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1003 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1003%nat states)=Some(Gtyp(global_type_at 1003%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::23] 0 (multiplier_ports 0) generated_module_0_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::23] 4 states)=Some(Gtyp(global_type_at 1003%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_0_4 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1007 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1007%nat states)=Some(Gtyp(global_type_at 1007%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::23] 0 (multiplier_ports 0) generated_module_0_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::23] 5 states)=Some(Gtyp(global_type_at 1007%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_0_5 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1010 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1010%nat states)=Some(Gtyp(global_type_at 1010%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 24 2 states)=Some(Gtyp(global_type_at 1010%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 24 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_24 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1013 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1013%nat states)=Some(Gtyp(global_type_at 1013%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 24 3 states)=Some(Gtyp(global_type_at 1013%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 24 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_24 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1021 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1021%nat states)=Some(Gtyp(global_type_at 1021%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::24] 0 (multiplier_ports 0) generated_module_0_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::24] 4 states)=Some(Gtyp(global_type_at 1021%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_0_4 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1025 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1025%nat states)=Some(Gtyp(global_type_at 1025%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::24] 0 (multiplier_ports 0) generated_module_0_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::24] 5 states)=Some(Gtyp(global_type_at 1025%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_0_5 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1028 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1028%nat states)=Some(Gtyp(global_type_at 1028%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 25 2 states)=Some(Gtyp(global_type_at 1028%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 25 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_25 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1031 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1031%nat states)=Some(Gtyp(global_type_at 1031%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 25 3 states)=Some(Gtyp(global_type_at 1031%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 25 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_25 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1039 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1039%nat states)=Some(Gtyp(global_type_at 1039%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::25] 0 (multiplier_ports 0) generated_module_0_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::25] 4 states)=Some(Gtyp(global_type_at 1039%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_0_4 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1043 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1043%nat states)=Some(Gtyp(global_type_at 1043%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::25] 0 (multiplier_ports 0) generated_module_0_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::25] 5 states)=Some(Gtyp(global_type_at 1043%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_0_5 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1046 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1046%nat states)=Some(Gtyp(global_type_at 1046%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 26 2 states)=Some(Gtyp(global_type_at 1046%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 26 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_26 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1049 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1049%nat states)=Some(Gtyp(global_type_at 1049%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 26 3 states)=Some(Gtyp(global_type_at 1049%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 26 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_26 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1057 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1057%nat states)=Some(Gtyp(global_type_at 1057%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::26] 0 (multiplier_ports 0) generated_module_0_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::26] 4 states)=Some(Gtyp(global_type_at 1057%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_0_4 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1061 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1061%nat states)=Some(Gtyp(global_type_at 1061%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::26] 0 (multiplier_ports 0) generated_module_0_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::26] 5 states)=Some(Gtyp(global_type_at 1061%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_0_5 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1064 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1064%nat states)=Some(Gtyp(global_type_at 1064%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 27 4 states)=Some(Gtyp(global_type_at 1064%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 27 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_27 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1067 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1067%nat states)=Some(Gtyp(global_type_at 1067%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 27 2 states)=Some(Gtyp(global_type_at 1067%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 27 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_27 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1070 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1070%nat states)=Some(Gtyp(global_type_at 1070%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 27 3 states)=Some(Gtyp(global_type_at 1070%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 27 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_27 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1081 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1081%nat states)=Some(Gtyp(global_type_at 1081%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::27] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::27] 5 states)=Some(Gtyp(global_type_at 1081%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_5 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1085 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1085%nat states)=Some(Gtyp(global_type_at 1085%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::27] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::27] 6 states)=Some(Gtyp(global_type_at 1085%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_6 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1088 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1088%nat states)=Some(Gtyp(global_type_at 1088%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 28 4 states)=Some(Gtyp(global_type_at 1088%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 28 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_28 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1091 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1091%nat states)=Some(Gtyp(global_type_at 1091%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 28 2 states)=Some(Gtyp(global_type_at 1091%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 28 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_28 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1094 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1094%nat states)=Some(Gtyp(global_type_at 1094%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 28 3 states)=Some(Gtyp(global_type_at 1094%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 28 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_28 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1105 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1105%nat states)=Some(Gtyp(global_type_at 1105%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::28] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::28] 5 states)=Some(Gtyp(global_type_at 1105%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_5 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1109 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1109%nat states)=Some(Gtyp(global_type_at 1109%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::28] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::28] 6 states)=Some(Gtyp(global_type_at 1109%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_6 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1112 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1112%nat states)=Some(Gtyp(global_type_at 1112%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 29 2 states)=Some(Gtyp(global_type_at 1112%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 29 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_29 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1115 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1115%nat states)=Some(Gtyp(global_type_at 1115%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 29 3 states)=Some(Gtyp(global_type_at 1115%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 29 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_29 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1123 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1123%nat states)=Some(Gtyp(global_type_at 1123%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::29] 0 (multiplier_ports 0) generated_module_0_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::29] 4 states)=Some(Gtyp(global_type_at 1123%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_0_4 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1127 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1127%nat states)=Some(Gtyp(global_type_at 1127%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::29] 0 (multiplier_ports 0) generated_module_0_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::29] 5 states)=Some(Gtyp(global_type_at 1127%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_0_5 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1130 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1130%nat states)=Some(Gtyp(global_type_at 1130%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 30 2 states)=Some(Gtyp(global_type_at 1130%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 30 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_30 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1133 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1133%nat states)=Some(Gtyp(global_type_at 1133%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 30 3 states)=Some(Gtyp(global_type_at 1133%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 30 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_30 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1141 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1141%nat states)=Some(Gtyp(global_type_at 1141%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::30] 0 (multiplier_ports 0) generated_module_0_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::30] 4 states)=Some(Gtyp(global_type_at 1141%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_0_4 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1145 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1145%nat states)=Some(Gtyp(global_type_at 1145%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::30] 0 (multiplier_ports 0) generated_module_0_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::30] 5 states)=Some(Gtyp(global_type_at 1145%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_0_5 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1148 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1148%nat states)=Some(Gtyp(global_type_at 1148%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 31 2 states)=Some(Gtyp(global_type_at 1148%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 31 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_31 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1151 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1151%nat states)=Some(Gtyp(global_type_at 1151%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 31 3 states)=Some(Gtyp(global_type_at 1151%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 31 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_31 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1159 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1159%nat states)=Some(Gtyp(global_type_at 1159%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::31] 0 (multiplier_ports 0) generated_module_0_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::31] 4 states)=Some(Gtyp(global_type_at 1159%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_0_4 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1163 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1163%nat states)=Some(Gtyp(global_type_at 1163%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::31] 0 (multiplier_ports 0) generated_module_0_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::31] 5 states)=Some(Gtyp(global_type_at 1163%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_0_5 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1166 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1166%nat states)=Some(Gtyp(global_type_at 1166%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 32 2 states)=Some(Gtyp(global_type_at 1166%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 32 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_32 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1169 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1169%nat states)=Some(Gtyp(global_type_at 1169%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 32 3 states)=Some(Gtyp(global_type_at 1169%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 32 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_32 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1177 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1177%nat states)=Some(Gtyp(global_type_at 1177%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::32] 0 (multiplier_ports 0) generated_module_0_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::32] 4 states)=Some(Gtyp(global_type_at 1177%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_0_4 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1181 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1181%nat states)=Some(Gtyp(global_type_at 1181%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::32] 0 (multiplier_ports 0) generated_module_0_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::32] 5 states)=Some(Gtyp(global_type_at 1181%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_0_5 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1184 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1184%nat states)=Some(Gtyp(global_type_at 1184%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 33 4 states)=Some(Gtyp(global_type_at 1184%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 33 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_33 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1187 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1187%nat states)=Some(Gtyp(global_type_at 1187%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 33 2 states)=Some(Gtyp(global_type_at 1187%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 33 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_33 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1190 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1190%nat states)=Some(Gtyp(global_type_at 1190%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 33 3 states)=Some(Gtyp(global_type_at 1190%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 33 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_33 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1201 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1201%nat states)=Some(Gtyp(global_type_at 1201%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::33] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::33] 5 states)=Some(Gtyp(global_type_at 1201%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_5 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1205 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1205%nat states)=Some(Gtyp(global_type_at 1205%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::33] 1 (multiplier_ports 1) generated_module_1_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::33] 6 states)=Some(Gtyp(global_type_at 1205%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_1_6 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1208 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1208%nat states)=Some(Gtyp(global_type_at 1208%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 34 2 states)=Some(Gtyp(global_type_at 1208%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 34 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_34 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1211 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1211%nat states)=Some(Gtyp(global_type_at 1211%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 34 3 states)=Some(Gtyp(global_type_at 1211%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 34 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_34 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1219 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1219%nat states)=Some(Gtyp(global_type_at 1219%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::34] 0 (multiplier_ports 0) generated_module_0_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::34] 4 states)=Some(Gtyp(global_type_at 1219%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_0_4 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1223 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1223%nat states)=Some(Gtyp(global_type_at 1223%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::34] 0 (multiplier_ports 0) generated_module_0_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::34] 5 states)=Some(Gtyp(global_type_at 1223%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_0_5 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1226 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1226%nat states)=Some(Gtyp(global_type_at 1226%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 35 2 states)=Some(Gtyp(global_type_at 1226%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 35 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_35 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1229 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1229%nat states)=Some(Gtyp(global_type_at 1229%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 35 3 states)=Some(Gtyp(global_type_at 1229%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 35 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_35 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1237 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1237%nat states)=Some(Gtyp(global_type_at 1237%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::35] 0 (multiplier_ports 0) generated_module_0_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::35] 4 states)=Some(Gtyp(global_type_at 1237%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_0_4 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1241 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1241%nat states)=Some(Gtyp(global_type_at 1241%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::35] 0 (multiplier_ports 0) generated_module_0_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::35] 5 states)=Some(Gtyp(global_type_at 1241%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_0_5 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1244 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1244%nat states)=Some(Gtyp(global_type_at 1244%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 36 2 states)=Some(Gtyp(global_type_at 1244%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 36 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_36 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1247 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1247%nat states)=Some(Gtyp(global_type_at 1247%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 36 3 states)=Some(Gtyp(global_type_at 1247%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 36 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_36 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1255 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1255%nat states)=Some(Gtyp(global_type_at 1255%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::36] 0 (multiplier_ports 0) generated_module_0_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::36] 4 states)=Some(Gtyp(global_type_at 1255%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_0_4 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1259 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1259%nat states)=Some(Gtyp(global_type_at 1259%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::36] 0 (multiplier_ports 0) generated_module_0_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::36] 5 states)=Some(Gtyp(global_type_at 1259%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (initial_output_0_5 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1299 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1299%nat states)=Some(Gtyp(global_type_at 1299%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_lookup [::] 6 states)=Some(Gtyp(global_type_at 1299%nat))).
 unfold circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 6 (ltac:(reflexivity))).
 rewrite (initial_output_3_6 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1310 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1310%nat states)=Some(Gtyp(global_type_at 1310%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 7 0 states)=Some(Gtyp(global_type_at 1310%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 7 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_7 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1311 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1311%nat states)=Some(Gtyp(global_type_at 1311%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 7 1 states)=Some(Gtyp(global_type_at 1311%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 7 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_7 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1312 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1312%nat states)=Some(Gtyp(global_type_at 1312%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 8 0 states)=Some(Gtyp(global_type_at 1312%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 8 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_8 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1313 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1313%nat states)=Some(Gtyp(global_type_at 1313%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 8 1 states)=Some(Gtyp(global_type_at 1313%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 8 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_8 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1314 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1314%nat states)=Some(Gtyp(global_type_at 1314%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 9 0 states)=Some(Gtyp(global_type_at 1314%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 9 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_9 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1315 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1315%nat states)=Some(Gtyp(global_type_at 1315%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 9 1 states)=Some(Gtyp(global_type_at 1315%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 9 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_9 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1316 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1316%nat states)=Some(Gtyp(global_type_at 1316%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 10 0 states)=Some(Gtyp(global_type_at 1316%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 10 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1317 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1317%nat states)=Some(Gtyp(global_type_at 1317%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 10 1 states)=Some(Gtyp(global_type_at 1317%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 10 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1318 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1318%nat states)=Some(Gtyp(global_type_at 1318%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 11 0 states)=Some(Gtyp(global_type_at 1318%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 11 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1319 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1319%nat states)=Some(Gtyp(global_type_at 1319%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 11 1 states)=Some(Gtyp(global_type_at 1319%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 11 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1320 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1320%nat states)=Some(Gtyp(global_type_at 1320%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 12 0 states)=Some(Gtyp(global_type_at 1320%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 12 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_12 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1321 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1321%nat states)=Some(Gtyp(global_type_at 1321%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 12 1 states)=Some(Gtyp(global_type_at 1321%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 12 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_12 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1322 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1322%nat states)=Some(Gtyp(global_type_at 1322%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 13 0 states)=Some(Gtyp(global_type_at 1322%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 13 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_13 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1323 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1323%nat states)=Some(Gtyp(global_type_at 1323%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 13 1 states)=Some(Gtyp(global_type_at 1323%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 13 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_13 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1324 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1324%nat states)=Some(Gtyp(global_type_at 1324%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 14 0 states)=Some(Gtyp(global_type_at 1324%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 14 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_14 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1325 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1325%nat states)=Some(Gtyp(global_type_at 1325%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 14 1 states)=Some(Gtyp(global_type_at 1325%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 14 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_14 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1326 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1326%nat states)=Some(Gtyp(global_type_at 1326%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 15 0 states)=Some(Gtyp(global_type_at 1326%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 15 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_15 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1327 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1327%nat states)=Some(Gtyp(global_type_at 1327%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 15 1 states)=Some(Gtyp(global_type_at 1327%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 15 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_15 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1328 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1328%nat states)=Some(Gtyp(global_type_at 1328%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 16 0 states)=Some(Gtyp(global_type_at 1328%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 16 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_16 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1329 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1329%nat states)=Some(Gtyp(global_type_at 1329%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 16 1 states)=Some(Gtyp(global_type_at 1329%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 16 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_16 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1330 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1330%nat states)=Some(Gtyp(global_type_at 1330%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 17 0 states)=Some(Gtyp(global_type_at 1330%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 17 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_17 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1331 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1331%nat states)=Some(Gtyp(global_type_at 1331%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 17 1 states)=Some(Gtyp(global_type_at 1331%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 17 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_17 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1332 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1332%nat states)=Some(Gtyp(global_type_at 1332%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 18 0 states)=Some(Gtyp(global_type_at 1332%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 18 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_18 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1333 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1333%nat states)=Some(Gtyp(global_type_at 1333%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 18 1 states)=Some(Gtyp(global_type_at 1333%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 18 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_18 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1334 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1334%nat states)=Some(Gtyp(global_type_at 1334%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 19 0 states)=Some(Gtyp(global_type_at 1334%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 19 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_19 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1335 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1335%nat states)=Some(Gtyp(global_type_at 1335%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 19 1 states)=Some(Gtyp(global_type_at 1335%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 19 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_19 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1336 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1336%nat states)=Some(Gtyp(global_type_at 1336%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 20 0 states)=Some(Gtyp(global_type_at 1336%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 20 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_20 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1337 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1337%nat states)=Some(Gtyp(global_type_at 1337%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 20 1 states)=Some(Gtyp(global_type_at 1337%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 20 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_20 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1338 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1338%nat states)=Some(Gtyp(global_type_at 1338%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 21 0 states)=Some(Gtyp(global_type_at 1338%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 21 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_21 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1339 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1339%nat states)=Some(Gtyp(global_type_at 1339%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 21 1 states)=Some(Gtyp(global_type_at 1339%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 21 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_21 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1340 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1340%nat states)=Some(Gtyp(global_type_at 1340%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 22 0 states)=Some(Gtyp(global_type_at 1340%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 22 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_22 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1341 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1341%nat states)=Some(Gtyp(global_type_at 1341%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 22 1 states)=Some(Gtyp(global_type_at 1341%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 22 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_22 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1342 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1342%nat states)=Some(Gtyp(global_type_at 1342%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 23 0 states)=Some(Gtyp(global_type_at 1342%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 23 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_23 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1343 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1343%nat states)=Some(Gtyp(global_type_at 1343%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 23 1 states)=Some(Gtyp(global_type_at 1343%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 23 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_23 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1344 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1344%nat states)=Some(Gtyp(global_type_at 1344%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 24 0 states)=Some(Gtyp(global_type_at 1344%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 24 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_24 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1345 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1345%nat states)=Some(Gtyp(global_type_at 1345%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 24 1 states)=Some(Gtyp(global_type_at 1345%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 24 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_24 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1346 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1346%nat states)=Some(Gtyp(global_type_at 1346%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 25 0 states)=Some(Gtyp(global_type_at 1346%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 25 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_25 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1347 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1347%nat states)=Some(Gtyp(global_type_at 1347%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 25 1 states)=Some(Gtyp(global_type_at 1347%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 25 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_25 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1348 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1348%nat states)=Some(Gtyp(global_type_at 1348%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 26 0 states)=Some(Gtyp(global_type_at 1348%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 26 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_26 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1349 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1349%nat states)=Some(Gtyp(global_type_at 1349%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 26 1 states)=Some(Gtyp(global_type_at 1349%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 26 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_26 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1350 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1350%nat states)=Some(Gtyp(global_type_at 1350%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 27 0 states)=Some(Gtyp(global_type_at 1350%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 27 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_27 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1351 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1351%nat states)=Some(Gtyp(global_type_at 1351%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 27 1 states)=Some(Gtyp(global_type_at 1351%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 27 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_27 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1352 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1352%nat states)=Some(Gtyp(global_type_at 1352%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 28 0 states)=Some(Gtyp(global_type_at 1352%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 28 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_28 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1353 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1353%nat states)=Some(Gtyp(global_type_at 1353%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 28 1 states)=Some(Gtyp(global_type_at 1353%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 28 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_28 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1354 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1354%nat states)=Some(Gtyp(global_type_at 1354%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 29 0 states)=Some(Gtyp(global_type_at 1354%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 29 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_29 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1355 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1355%nat states)=Some(Gtyp(global_type_at 1355%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 29 1 states)=Some(Gtyp(global_type_at 1355%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 29 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_29 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1356 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1356%nat states)=Some(Gtyp(global_type_at 1356%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 30 0 states)=Some(Gtyp(global_type_at 1356%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 30 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_30 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1357 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1357%nat states)=Some(Gtyp(global_type_at 1357%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 30 1 states)=Some(Gtyp(global_type_at 1357%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 30 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_30 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1358 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1358%nat states)=Some(Gtyp(global_type_at 1358%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 31 0 states)=Some(Gtyp(global_type_at 1358%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 31 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_31 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1359 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1359%nat states)=Some(Gtyp(global_type_at 1359%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 31 1 states)=Some(Gtyp(global_type_at 1359%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 31 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_31 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1360 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1360%nat states)=Some(Gtyp(global_type_at 1360%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 32 0 states)=Some(Gtyp(global_type_at 1360%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 32 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_32 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1361 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1361%nat states)=Some(Gtyp(global_type_at 1361%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 32 1 states)=Some(Gtyp(global_type_at 1361%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 32 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_32 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1362 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1362%nat states)=Some(Gtyp(global_type_at 1362%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 33 0 states)=Some(Gtyp(global_type_at 1362%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 33 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_33 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1363 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1363%nat states)=Some(Gtyp(global_type_at 1363%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 33 1 states)=Some(Gtyp(global_type_at 1363%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 33 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_33 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1364 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1364%nat states)=Some(Gtyp(global_type_at 1364%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 34 0 states)=Some(Gtyp(global_type_at 1364%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 34 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_34 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1365 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1365%nat states)=Some(Gtyp(global_type_at 1365%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 34 1 states)=Some(Gtyp(global_type_at 1365%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 34 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_34 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1366 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1366%nat states)=Some(Gtyp(global_type_at 1366%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 35 0 states)=Some(Gtyp(global_type_at 1366%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 35 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_35 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1367 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1367%nat states)=Some(Gtyp(global_type_at 1367%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 35 1 states)=Some(Gtyp(global_type_at 1367%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 35 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_35 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1368 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1368%nat states)=Some(Gtyp(global_type_at 1368%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 36 0 states)=Some(Gtyp(global_type_at 1368%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 36 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_36 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1369 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1369%nat states)=Some(Gtyp(global_type_at 1369%nat)).
Proof.
 destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::] 36 1 states)=Some(Gtyp(global_type_at 1369%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (multiplier_external_private v env 36 (ltac:(reflexivity))).
 rewrite (initial_bundle_3_36 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1464 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1464%nat states)=Some(Gtyp(global_type_at 1464%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::11] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::11] 10 0 states)=Some(Gtyp(global_type_at 1464%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1465 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1465%nat states)=Some(Gtyp(global_type_at 1465%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::11] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::11] 10 1 states)=Some(Gtyp(global_type_at 1465%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1466 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1466%nat states)=Some(Gtyp(global_type_at 1466%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::11] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::11] 11 0 states)=Some(Gtyp(global_type_at 1466%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1467 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1467%nat states)=Some(Gtyp(global_type_at 1467%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::11] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::11] 11 1 states)=Some(Gtyp(global_type_at 1467%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1532 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1532%nat states)=Some(Gtyp(global_type_at 1532%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::12] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::12] 10 0 states)=Some(Gtyp(global_type_at 1532%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1533 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1533%nat states)=Some(Gtyp(global_type_at 1533%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::12] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::12] 10 1 states)=Some(Gtyp(global_type_at 1533%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1534 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1534%nat states)=Some(Gtyp(global_type_at 1534%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::12] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::12] 11 0 states)=Some(Gtyp(global_type_at 1534%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1535 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1535%nat states)=Some(Gtyp(global_type_at 1535%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::12] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::12] 11 1 states)=Some(Gtyp(global_type_at 1535%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1600 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1600%nat states)=Some(Gtyp(global_type_at 1600%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::13] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::13] 10 0 states)=Some(Gtyp(global_type_at 1600%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1601 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1601%nat states)=Some(Gtyp(global_type_at 1601%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::13] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::13] 10 1 states)=Some(Gtyp(global_type_at 1601%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1602 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1602%nat states)=Some(Gtyp(global_type_at 1602%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::13] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::13] 11 0 states)=Some(Gtyp(global_type_at 1602%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1603 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1603%nat states)=Some(Gtyp(global_type_at 1603%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::13] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::13] 11 1 states)=Some(Gtyp(global_type_at 1603%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1668 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1668%nat states)=Some(Gtyp(global_type_at 1668%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::14] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::14] 10 0 states)=Some(Gtyp(global_type_at 1668%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1669 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1669%nat states)=Some(Gtyp(global_type_at 1669%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::14] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::14] 10 1 states)=Some(Gtyp(global_type_at 1669%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1670 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1670%nat states)=Some(Gtyp(global_type_at 1670%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::14] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::14] 11 0 states)=Some(Gtyp(global_type_at 1670%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1671 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1671%nat states)=Some(Gtyp(global_type_at 1671%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::14] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::14] 11 1 states)=Some(Gtyp(global_type_at 1671%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1736 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1736%nat states)=Some(Gtyp(global_type_at 1736%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::15] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::15] 10 0 states)=Some(Gtyp(global_type_at 1736%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1737 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1737%nat states)=Some(Gtyp(global_type_at 1737%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::15] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::15] 10 1 states)=Some(Gtyp(global_type_at 1737%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1738 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1738%nat states)=Some(Gtyp(global_type_at 1738%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::15] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::15] 11 0 states)=Some(Gtyp(global_type_at 1738%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1739 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1739%nat states)=Some(Gtyp(global_type_at 1739%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::15] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::15] 11 1 states)=Some(Gtyp(global_type_at 1739%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1804 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1804%nat states)=Some(Gtyp(global_type_at 1804%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::16] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::16] 10 0 states)=Some(Gtyp(global_type_at 1804%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1805 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1805%nat states)=Some(Gtyp(global_type_at 1805%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::16] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::16] 10 1 states)=Some(Gtyp(global_type_at 1805%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1806 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1806%nat states)=Some(Gtyp(global_type_at 1806%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::16] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::16] 11 0 states)=Some(Gtyp(global_type_at 1806%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1807 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1807%nat states)=Some(Gtyp(global_type_at 1807%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::16] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::16] 11 1 states)=Some(Gtyp(global_type_at 1807%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1872 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1872%nat states)=Some(Gtyp(global_type_at 1872%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::17] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::17] 10 0 states)=Some(Gtyp(global_type_at 1872%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1873 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1873%nat states)=Some(Gtyp(global_type_at 1873%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::17] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::17] 10 1 states)=Some(Gtyp(global_type_at 1873%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1874 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1874%nat states)=Some(Gtyp(global_type_at 1874%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::17] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::17] 11 0 states)=Some(Gtyp(global_type_at 1874%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1875 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1875%nat states)=Some(Gtyp(global_type_at 1875%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::17] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::17] 11 1 states)=Some(Gtyp(global_type_at 1875%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1940 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1940%nat states)=Some(Gtyp(global_type_at 1940%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::18] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::18] 10 0 states)=Some(Gtyp(global_type_at 1940%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1941 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1941%nat states)=Some(Gtyp(global_type_at 1941%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::18] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::18] 10 1 states)=Some(Gtyp(global_type_at 1941%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_10 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1942 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1942%nat states)=Some(Gtyp(global_type_at 1942%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::18] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::18] 11 0 states)=Some(Gtyp(global_type_at 1942%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
Lemma initial_type_1943 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at 1943%nat states)=Some(Gtyp(global_type_at 1943%nat)).
Proof.
 destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances [::18] 2 (multiplier_ports 2) generated_module_2_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
 change (option_map type_of_val(circuit_interface [::18] 11 1 states)=Some(Gtyp(global_type_at 1943%nat))).
 unfold circuit_interface,circuit_lookup. rewrite Found.
 rewrite (initial_bundle_2_11 _ env Initial). reflexivity.
Qed.
