From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import HierarchyFacts PortFieldFacts FieldTypes.
From SmallMultiplier Require Import Model GlobalStable GlobalLocal GlobalMemory GlobalInstances GlobalFieldFacts InstanceChecks FieldWrites.
Local Open Scope N_scope.
Lemma global_field_278_sync : field_sync_check generated_modules multiplier_instances [::] 7 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_278_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 7 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 7 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_278).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_7_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_278_sync.
 - exact ran.
Qed.
Lemma global_field_278_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 201 snapshot = Some (Gval (Fuint 1) (global_word_3 v)))
 (initial_field : circuit_interface [::] 7 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_278 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_278 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 7 2 final = Some (Gval (Fuint 1) (global_word_278 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_278) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_7_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_278. apply global_local_278.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_278_sync.
 - exact ran.
Qed.
Lemma global_field_281_sync : field_sync_check generated_modules multiplier_instances [::] 7 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_281_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 7 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 7 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_281).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_7_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_281_sync.
 - exact ran.
Qed.
Lemma global_field_281_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 203 snapshot = Some (Gval (Fuint 1) (global_word_4 v)))
 (initial_field : circuit_interface [::] 7 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_281 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_281 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 7 3 final = Some (Gval (Fuint 1) (global_word_281 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_281) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_7_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_281. apply global_local_281.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_281_sync.
 - exact ran.
Qed.
Lemma global_field_296_sync : field_sync_check generated_modules multiplier_instances [::] 8 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_296_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 8 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 8 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_296).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_8_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_296_sync.
 - exact ran.
Qed.
Lemma global_field_296_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 205 snapshot = Some (Gval (Fuint 1) (global_word_5 v)))
 (initial_field : circuit_interface [::] 8 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_296 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_296 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 8 2 final = Some (Gval (Fuint 1) (global_word_296 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_296) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_8_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_296. apply global_local_296.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_296_sync.
 - exact ran.
Qed.
Lemma global_field_299_sync : field_sync_check generated_modules multiplier_instances [::] 8 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_299_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 8 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 8 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_299).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_8_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_299_sync.
 - exact ran.
Qed.
Lemma global_field_299_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 207 snapshot = Some (Gval (Fuint 1) (global_word_6 v)))
 (initial_field : circuit_interface [::] 8 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_299 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_299 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 8 3 final = Some (Gval (Fuint 1) (global_word_299 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_299) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_8_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_299. apply global_local_299.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_299_sync.
 - exact ran.
Qed.
Lemma global_field_314_sync : field_sync_check generated_modules multiplier_instances [::] 9 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_314_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 9 4 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 9 4 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_314).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_9_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_314_sync.
 - exact ran.
Qed.
Lemma global_field_314_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 213 snapshot = Some (Gval (Fuint 1) (global_word_9 v)))
 (initial_field : circuit_interface [::] 9 4 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_314 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_314 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 9 4 final = Some (Gval (Fuint 1) (global_word_314 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_314) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_9_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_314. apply global_local_314.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_314_sync.
 - exact ran.
Qed.
Lemma global_field_317_sync : field_sync_check generated_modules multiplier_instances [::] 9 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_317_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 9 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 9 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_317).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_9_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_317_sync.
 - exact ran.
Qed.
Lemma global_field_317_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 209 snapshot = Some (Gval (Fuint 1) (global_word_7 v)))
 (initial_field : circuit_interface [::] 9 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_317 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_317 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 9 2 final = Some (Gval (Fuint 1) (global_word_317 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_317) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_9_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_317. apply global_local_317.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_317_sync.
 - exact ran.
Qed.
Lemma global_field_320_sync : field_sync_check generated_modules multiplier_instances [::] 9 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_320_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 9 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 9 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_320).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_9_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_320_sync.
 - exact ran.
Qed.
Lemma global_field_320_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 211 snapshot = Some (Gval (Fuint 1) (global_word_8 v)))
 (initial_field : circuit_interface [::] 9 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_320 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_320 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 9 3 final = Some (Gval (Fuint 1) (global_word_320 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_320) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_9_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_320. apply global_local_320.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_320_sync.
 - exact ran.
Qed.
Lemma global_field_338_sync : field_sync_check generated_modules multiplier_instances [::] 10 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_338_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 10 4 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 10 4 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_338).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_10_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_338_sync.
 - exact ran.
Qed.
Lemma global_field_338_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 219 snapshot = Some (Gval (Fuint 1) (global_word_12 v)))
 (initial_field : circuit_interface [::] 10 4 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_338 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_338 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 10 4 final = Some (Gval (Fuint 1) (global_word_338 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_338) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_10_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_338. apply global_local_338.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_338_sync.
 - exact ran.
Qed.
Lemma global_field_341_sync : field_sync_check generated_modules multiplier_instances [::] 10 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_341_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 10 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 10 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_341).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_10_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_341_sync.
 - exact ran.
Qed.
Lemma global_field_341_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 215 snapshot = Some (Gval (Fuint 1) (global_word_10 v)))
 (initial_field : circuit_interface [::] 10 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_341 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_341 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 10 2 final = Some (Gval (Fuint 1) (global_word_341 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_341) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_10_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_341. apply global_local_341.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_341_sync.
 - exact ran.
Qed.
Lemma global_field_344_sync : field_sync_check generated_modules multiplier_instances [::] 10 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_344_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 10 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 10 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_344).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_10_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_344_sync.
 - exact ran.
Qed.
Lemma global_field_344_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 217 snapshot = Some (Gval (Fuint 1) (global_word_11 v)))
 (initial_field : circuit_interface [::] 10 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_344 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_344 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 10 3 final = Some (Gval (Fuint 1) (global_word_344 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_344) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_10_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_344. apply global_local_344.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_344_sync.
 - exact ran.
Qed.
Lemma global_field_362_sync : field_sync_check generated_modules multiplier_instances [::] 11 6 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_362_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 11 6 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 11 6 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_362).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_11_6_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_362_sync.
 - exact ran.
Qed.
Lemma global_field_362_step invalid snapshot final v initial
 (initial_field : circuit_interface [::] 11 6 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_362 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_362 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 11 6 final = Some (Gval (Fuint 1) (global_word_362 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_362) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_11_6_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_362. apply global_local_362.
 - exact adapted.
 - reflexivity.
 - exact global_field_362_sync.
 - exact ran.
Qed.
Lemma global_field_365_sync : field_sync_check generated_modules multiplier_instances [::11] 11 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_365_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::11] 11 4 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::11] 11 4 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_365).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_365_sync.
 - exact ran.
Qed.
Lemma global_field_365_step invalid snapshot final v initial
 (H0 : circuit_lookup [::11] 40 snapshot = Some (Gval (Fuint 1) (global_word_364 v)))
 (initial_field : circuit_interface [::11] 11 4 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_365 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_365 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::11] 11 4 final = Some (Gval (Fuint 1) (global_word_365 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_365) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_365. apply global_local_365.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_365_sync.
 - exact ran.
Qed.
Lemma global_field_368_sync : field_sync_check generated_modules multiplier_instances [::] 11 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_368_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 11 4 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 11 4 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_368).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_11_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_368_sync.
 - exact ran.
Qed.
Lemma global_field_368_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 225 snapshot = Some (Gval (Fuint 1) (global_word_15 v)))
 (initial_field : circuit_interface [::] 11 4 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_368 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_368 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 11 4 final = Some (Gval (Fuint 1) (global_word_368 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_368) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_11_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_368. apply global_local_368.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_368_sync.
 - exact ran.
Qed.
Lemma global_field_370_sync : field_sync_check generated_modules multiplier_instances [::11] 10 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_370_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::11] 10 4 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::11] 10 4 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_370).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_370_sync.
 - exact ran.
Qed.
Lemma global_field_370_step invalid snapshot final v initial
 (H0 : circuit_lookup [::11] 4 snapshot = Some (Gval (Fuint 1) (global_word_369 v)))
 (initial_field : circuit_interface [::11] 10 4 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_370 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_370 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::11] 10 4 final = Some (Gval (Fuint 1) (global_word_370 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_370) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_370. apply global_local_370.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_370_sync.
 - exact ran.
Qed.
Lemma global_field_373_sync : field_sync_check generated_modules multiplier_instances [::] 11 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_373_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 11 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 11 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_373).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_11_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_373_sync.
 - exact ran.
Qed.
Lemma global_field_373_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 221 snapshot = Some (Gval (Fuint 1) (global_word_13 v)))
 (initial_field : circuit_interface [::] 11 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_373 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_373 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 11 2 final = Some (Gval (Fuint 1) (global_word_373 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_373) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_11_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_373. apply global_local_373.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_373_sync.
 - exact ran.
Qed.
Lemma global_field_375_sync : field_sync_check generated_modules multiplier_instances [::11] 10 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_375_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::11] 10 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::11] 10 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_375).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_375_sync.
 - exact ran.
Qed.
Lemma global_field_375_step invalid snapshot final v initial
 (H0 : circuit_lookup [::11] 2 snapshot = Some (Gval (Fuint 1) (global_word_374 v)))
 (initial_field : circuit_interface [::11] 10 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_375 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_375 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::11] 10 2 final = Some (Gval (Fuint 1) (global_word_375 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_375) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_375. apply global_local_375.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_375_sync.
 - exact ran.
Qed.
Lemma global_field_378_sync : field_sync_check generated_modules multiplier_instances [::] 11 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_378_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 11 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 11 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_378).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_11_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_378_sync.
 - exact ran.
Qed.
Lemma global_field_378_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 223 snapshot = Some (Gval (Fuint 1) (global_word_14 v)))
 (initial_field : circuit_interface [::] 11 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_378 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_378 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 11 3 final = Some (Gval (Fuint 1) (global_word_378 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_378) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_11_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_378. apply global_local_378.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_378_sync.
 - exact ran.
Qed.
Lemma global_field_380_sync : field_sync_check generated_modules multiplier_instances [::11] 10 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_380_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::11] 10 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::11] 10 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_380).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_380_sync.
 - exact ran.
Qed.
Lemma global_field_380_step invalid snapshot final v initial
 (H0 : circuit_lookup [::11] 3 snapshot = Some (Gval (Fuint 1) (global_word_379 v)))
 (initial_field : circuit_interface [::11] 10 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_380 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_380 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::11] 10 3 final = Some (Gval (Fuint 1) (global_word_380 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_380) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_380. apply global_local_380.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_380_sync.
 - exact ran.
Qed.
Lemma global_field_394_sync : field_sync_check generated_modules multiplier_instances [::11] 11 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_394_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::11] 11 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::11] 11 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_394).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_394_sync.
 - exact ran.
Qed.
Lemma global_field_394_step invalid snapshot final v initial
 (H0 : circuit_lookup [::11] 38 snapshot = Some (Gval (Fuint 1) (global_word_393 v)))
 (initial_field : circuit_interface [::11] 11 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_394 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_394 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::11] 11 2 final = Some (Gval (Fuint 1) (global_word_394 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_394) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_394. apply global_local_394.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_394_sync.
 - exact ran.
Qed.
Lemma global_field_397_sync : field_sync_check generated_modules multiplier_instances [::] 11 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_397_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 11 5 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 11 5 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_397).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_11_5_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_397_sync.
 - exact ran.
Qed.
Lemma global_field_397_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 227 snapshot = Some (Gval (Fuint 1) (global_word_16 v)))
 (initial_field : circuit_interface [::] 11 5 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_397 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_397 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 11 5 final = Some (Gval (Fuint 1) (global_word_397 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_397) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_11_5_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_397. apply global_local_397.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_397_sync.
 - exact ran.
Qed.
Lemma global_field_400_sync : field_sync_check generated_modules multiplier_instances [::11] 11 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_400_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::11] 11 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::11] 11 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_400).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_400_sync.
 - exact ran.
Qed.
Lemma global_field_400_step invalid snapshot final v initial
 (H0 : circuit_lookup [::11] 39 snapshot = Some (Gval (Fuint 1) (global_word_399 v)))
 (initial_field : circuit_interface [::11] 11 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_400 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_400 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::11] 11 3 final = Some (Gval (Fuint 1) (global_word_400 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_400) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_400. apply global_local_400.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_400_sync.
 - exact ran.
Qed.
Lemma global_field_431_sync : field_sync_check generated_modules multiplier_instances [::] 12 6 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_431_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 12 6 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 12 6 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_431).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_12_6_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_431_sync.
 - exact ran.
Qed.
Lemma global_field_431_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 314 snapshot = Some (Gval (Fuint 1) (global_word_423 v)))
 (initial_field : circuit_interface [::] 12 6 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_431 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_431 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 12 6 final = Some (Gval (Fuint 1) (global_word_431 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_431) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_12_6_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_431. apply global_local_431.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_431_sync.
 - exact ran.
Qed.
Lemma global_field_434_sync : field_sync_check generated_modules multiplier_instances [::12] 11 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_434_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::12] 11 4 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::12] 11 4 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_434).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_434_sync.
 - exact ran.
Qed.
Lemma global_field_434_step invalid snapshot final v initial
 (H0 : circuit_lookup [::12] 40 snapshot = Some (Gval (Fuint 1) (global_word_433 v)))
 (initial_field : circuit_interface [::12] 11 4 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_434 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_434 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::12] 11 4 final = Some (Gval (Fuint 1) (global_word_434 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_434) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_434. apply global_local_434.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_434_sync.
 - exact ran.
Qed.
Lemma global_field_437_sync : field_sync_check generated_modules multiplier_instances [::] 12 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_437_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 12 4 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 12 4 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_437).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_12_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_437_sync.
 - exact ran.
Qed.
Lemma global_field_437_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 233 snapshot = Some (Gval (Fuint 1) (global_word_19 v)))
 (initial_field : circuit_interface [::] 12 4 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_437 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_437 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 12 4 final = Some (Gval (Fuint 1) (global_word_437 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_437) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_12_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_437. apply global_local_437.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_437_sync.
 - exact ran.
Qed.
Lemma global_field_439_sync : field_sync_check generated_modules multiplier_instances [::12] 10 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_439_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::12] 10 4 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::12] 10 4 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_439).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_439_sync.
 - exact ran.
Qed.
Lemma global_field_439_step invalid snapshot final v initial
 (H0 : circuit_lookup [::12] 4 snapshot = Some (Gval (Fuint 1) (global_word_438 v)))
 (initial_field : circuit_interface [::12] 10 4 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_439 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_439 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::12] 10 4 final = Some (Gval (Fuint 1) (global_word_439 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_439) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_439. apply global_local_439.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_439_sync.
 - exact ran.
Qed.
Lemma global_field_442_sync : field_sync_check generated_modules multiplier_instances [::] 12 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_442_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 12 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 12 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_442).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_12_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_442_sync.
 - exact ran.
Qed.
Lemma global_field_442_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 229 snapshot = Some (Gval (Fuint 1) (global_word_17 v)))
 (initial_field : circuit_interface [::] 12 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_442 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_442 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 12 2 final = Some (Gval (Fuint 1) (global_word_442 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_442) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_12_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_442. apply global_local_442.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_442_sync.
 - exact ran.
Qed.
Lemma global_field_444_sync : field_sync_check generated_modules multiplier_instances [::12] 10 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_444_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::12] 10 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::12] 10 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_444).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_444_sync.
 - exact ran.
Qed.
Lemma global_field_444_step invalid snapshot final v initial
 (H0 : circuit_lookup [::12] 2 snapshot = Some (Gval (Fuint 1) (global_word_443 v)))
 (initial_field : circuit_interface [::12] 10 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_444 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_444 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::12] 10 2 final = Some (Gval (Fuint 1) (global_word_444 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_444) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_444. apply global_local_444.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_444_sync.
 - exact ran.
Qed.
Lemma global_field_447_sync : field_sync_check generated_modules multiplier_instances [::] 12 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_447_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 12 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 12 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_447).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_12_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_447_sync.
 - exact ran.
Qed.
Lemma global_field_447_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 231 snapshot = Some (Gval (Fuint 1) (global_word_18 v)))
 (initial_field : circuit_interface [::] 12 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_447 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_447 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 12 3 final = Some (Gval (Fuint 1) (global_word_447 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_447) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_12_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_447. apply global_local_447.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_447_sync.
 - exact ran.
Qed.
Lemma global_field_449_sync : field_sync_check generated_modules multiplier_instances [::12] 10 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_449_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::12] 10 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::12] 10 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_449).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_449_sync.
 - exact ran.
Qed.
Lemma global_field_449_step invalid snapshot final v initial
 (H0 : circuit_lookup [::12] 3 snapshot = Some (Gval (Fuint 1) (global_word_448 v)))
 (initial_field : circuit_interface [::12] 10 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_449 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_449 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::12] 10 3 final = Some (Gval (Fuint 1) (global_word_449 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_449) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_449. apply global_local_449.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_449_sync.
 - exact ran.
Qed.
Lemma global_field_463_sync : field_sync_check generated_modules multiplier_instances [::12] 11 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_463_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::12] 11 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::12] 11 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_463).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_463_sync.
 - exact ran.
Qed.
Lemma global_field_463_step invalid snapshot final v initial
 (H0 : circuit_lookup [::12] 38 snapshot = Some (Gval (Fuint 1) (global_word_462 v)))
 (initial_field : circuit_interface [::12] 11 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_463 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_463 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::12] 11 2 final = Some (Gval (Fuint 1) (global_word_463 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_463) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_463. apply global_local_463.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_463_sync.
 - exact ran.
Qed.
Lemma global_field_466_sync : field_sync_check generated_modules multiplier_instances [::] 12 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_466_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 12 5 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 12 5 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_466).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_12_5_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_466_sync.
 - exact ran.
Qed.
Lemma global_field_466_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 235 snapshot = Some (Gval (Fuint 1) (global_word_20 v)))
 (initial_field : circuit_interface [::] 12 5 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_466 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_466 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 12 5 final = Some (Gval (Fuint 1) (global_word_466 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_466) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_12_5_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_466. apply global_local_466.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_466_sync.
 - exact ran.
Qed.
Lemma global_field_469_sync : field_sync_check generated_modules multiplier_instances [::12] 11 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_469_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::12] 11 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::12] 11 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_469).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_469_sync.
 - exact ran.
Qed.
Lemma global_field_469_step invalid snapshot final v initial
 (H0 : circuit_lookup [::12] 39 snapshot = Some (Gval (Fuint 1) (global_word_468 v)))
 (initial_field : circuit_interface [::12] 11 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_469 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_469 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::12] 11 3 final = Some (Gval (Fuint 1) (global_word_469 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_469) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_469. apply global_local_469.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_469_sync.
 - exact ran.
Qed.
Lemma global_field_500_sync : field_sync_check generated_modules multiplier_instances [::] 13 6 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_500_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 13 6 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 13 6 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_500).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_13_6_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_500_sync.
 - exact ran.
Qed.
Lemma global_field_500_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 317 snapshot = Some (Gval (Fuint 1) (global_word_492 v)))
 (initial_field : circuit_interface [::] 13 6 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_500 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_500 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 13 6 final = Some (Gval (Fuint 1) (global_word_500 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_500) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_13_6_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_500. apply global_local_500.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_500_sync.
 - exact ran.
Qed.
Lemma global_field_503_sync : field_sync_check generated_modules multiplier_instances [::13] 11 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_503_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::13] 11 4 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::13] 11 4 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_503).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_503_sync.
 - exact ran.
Qed.
Lemma global_field_503_step invalid snapshot final v initial
 (H0 : circuit_lookup [::13] 40 snapshot = Some (Gval (Fuint 1) (global_word_502 v)))
 (initial_field : circuit_interface [::13] 11 4 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_503 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_503 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::13] 11 4 final = Some (Gval (Fuint 1) (global_word_503 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_503) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_503. apply global_local_503.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_503_sync.
 - exact ran.
Qed.
Lemma global_field_506_sync : field_sync_check generated_modules multiplier_instances [::] 13 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_506_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 13 4 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 13 4 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_506).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_13_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_506_sync.
 - exact ran.
Qed.
Lemma global_field_506_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 241 snapshot = Some (Gval (Fuint 1) (global_word_23 v)))
 (initial_field : circuit_interface [::] 13 4 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_506 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_506 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 13 4 final = Some (Gval (Fuint 1) (global_word_506 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_506) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_13_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_506. apply global_local_506.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_506_sync.
 - exact ran.
Qed.
Lemma global_field_508_sync : field_sync_check generated_modules multiplier_instances [::13] 10 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_508_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::13] 10 4 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::13] 10 4 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_508).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_508_sync.
 - exact ran.
Qed.
Lemma global_field_508_step invalid snapshot final v initial
 (H0 : circuit_lookup [::13] 4 snapshot = Some (Gval (Fuint 1) (global_word_507 v)))
 (initial_field : circuit_interface [::13] 10 4 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_508 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_508 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::13] 10 4 final = Some (Gval (Fuint 1) (global_word_508 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_508) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_508. apply global_local_508.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_508_sync.
 - exact ran.
Qed.
Lemma global_field_511_sync : field_sync_check generated_modules multiplier_instances [::] 13 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_511_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 13 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 13 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_511).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_13_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_511_sync.
 - exact ran.
Qed.
Lemma global_field_511_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 237 snapshot = Some (Gval (Fuint 1) (global_word_21 v)))
 (initial_field : circuit_interface [::] 13 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_511 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_511 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 13 2 final = Some (Gval (Fuint 1) (global_word_511 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_511) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_13_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_511. apply global_local_511.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_511_sync.
 - exact ran.
Qed.
Lemma global_field_513_sync : field_sync_check generated_modules multiplier_instances [::13] 10 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_513_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::13] 10 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::13] 10 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_513).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_513_sync.
 - exact ran.
Qed.
Lemma global_field_513_step invalid snapshot final v initial
 (H0 : circuit_lookup [::13] 2 snapshot = Some (Gval (Fuint 1) (global_word_512 v)))
 (initial_field : circuit_interface [::13] 10 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_513 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_513 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::13] 10 2 final = Some (Gval (Fuint 1) (global_word_513 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_513) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_513. apply global_local_513.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_513_sync.
 - exact ran.
Qed.
Lemma global_field_516_sync : field_sync_check generated_modules multiplier_instances [::] 13 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_516_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 13 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 13 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_516).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_13_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_516_sync.
 - exact ran.
Qed.
Lemma global_field_516_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 239 snapshot = Some (Gval (Fuint 1) (global_word_22 v)))
 (initial_field : circuit_interface [::] 13 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_516 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_516 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 13 3 final = Some (Gval (Fuint 1) (global_word_516 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_516) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_13_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_516. apply global_local_516.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_516_sync.
 - exact ran.
Qed.
Lemma global_field_518_sync : field_sync_check generated_modules multiplier_instances [::13] 10 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_518_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::13] 10 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::13] 10 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_518).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_518_sync.
 - exact ran.
Qed.
Lemma global_field_518_step invalid snapshot final v initial
 (H0 : circuit_lookup [::13] 3 snapshot = Some (Gval (Fuint 1) (global_word_517 v)))
 (initial_field : circuit_interface [::13] 10 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_518 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_518 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::13] 10 3 final = Some (Gval (Fuint 1) (global_word_518 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_518) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_518. apply global_local_518.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_518_sync.
 - exact ran.
Qed.
Lemma global_field_532_sync : field_sync_check generated_modules multiplier_instances [::13] 11 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_532_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::13] 11 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::13] 11 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_532).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_532_sync.
 - exact ran.
Qed.
Lemma global_field_532_step invalid snapshot final v initial
 (H0 : circuit_lookup [::13] 38 snapshot = Some (Gval (Fuint 1) (global_word_531 v)))
 (initial_field : circuit_interface [::13] 11 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_532 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_532 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::13] 11 2 final = Some (Gval (Fuint 1) (global_word_532 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_532) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_532. apply global_local_532.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_532_sync.
 - exact ran.
Qed.
Lemma global_field_535_sync : field_sync_check generated_modules multiplier_instances [::] 13 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_535_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 13 5 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 13 5 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_535).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_13_5_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_535_sync.
 - exact ran.
Qed.
Lemma global_field_535_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 243 snapshot = Some (Gval (Fuint 1) (global_word_24 v)))
 (initial_field : circuit_interface [::] 13 5 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_535 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_535 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 13 5 final = Some (Gval (Fuint 1) (global_word_535 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_535) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_13_5_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_535. apply global_local_535.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_535_sync.
 - exact ran.
Qed.
Lemma global_field_538_sync : field_sync_check generated_modules multiplier_instances [::13] 11 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_538_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::13] 11 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::13] 11 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_538).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_538_sync.
 - exact ran.
Qed.
Lemma global_field_538_step invalid snapshot final v initial
 (H0 : circuit_lookup [::13] 39 snapshot = Some (Gval (Fuint 1) (global_word_537 v)))
 (initial_field : circuit_interface [::13] 11 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_538 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_538 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::13] 11 3 final = Some (Gval (Fuint 1) (global_word_538 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_538) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_538. apply global_local_538.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_538_sync.
 - exact ran.
Qed.
Lemma global_field_569_sync : field_sync_check generated_modules multiplier_instances [::] 14 6 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_569_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 14 6 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 14 6 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_569).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_14_6_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_569_sync.
 - exact ran.
Qed.
Lemma global_field_569_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 320 snapshot = Some (Gval (Fuint 1) (global_word_561 v)))
 (initial_field : circuit_interface [::] 14 6 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_569 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_569 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 14 6 final = Some (Gval (Fuint 1) (global_word_569 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_569) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_14_6_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_569. apply global_local_569.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_569_sync.
 - exact ran.
Qed.
Lemma global_field_572_sync : field_sync_check generated_modules multiplier_instances [::14] 11 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_572_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::14] 11 4 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::14] 11 4 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_572).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_572_sync.
 - exact ran.
Qed.
Lemma global_field_572_step invalid snapshot final v initial
 (H0 : circuit_lookup [::14] 40 snapshot = Some (Gval (Fuint 1) (global_word_571 v)))
 (initial_field : circuit_interface [::14] 11 4 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_572 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_572 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::14] 11 4 final = Some (Gval (Fuint 1) (global_word_572 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_572) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_572. apply global_local_572.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_572_sync.
 - exact ran.
Qed.
Lemma global_field_575_sync : field_sync_check generated_modules multiplier_instances [::] 14 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_575_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 14 4 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 14 4 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_575).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_14_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_575_sync.
 - exact ran.
Qed.
Lemma global_field_575_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 251 snapshot = Some (Gval (Fuint 1) (global_word_28 v)))
 (initial_field : circuit_interface [::] 14 4 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_575 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_575 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 14 4 final = Some (Gval (Fuint 1) (global_word_575 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_575) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_14_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_575. apply global_local_575.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_575_sync.
 - exact ran.
Qed.
Lemma global_field_577_sync : field_sync_check generated_modules multiplier_instances [::14] 10 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_577_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::14] 10 4 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::14] 10 4 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_577).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_577_sync.
 - exact ran.
Qed.
Lemma global_field_577_step invalid snapshot final v initial
 (H0 : circuit_lookup [::14] 4 snapshot = Some (Gval (Fuint 1) (global_word_576 v)))
 (initial_field : circuit_interface [::14] 10 4 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_577 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_577 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::14] 10 4 final = Some (Gval (Fuint 1) (global_word_577 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_577) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_577. apply global_local_577.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_577_sync.
 - exact ran.
Qed.
Lemma global_field_580_sync : field_sync_check generated_modules multiplier_instances [::] 14 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_580_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 14 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 14 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_580).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_14_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_580_sync.
 - exact ran.
Qed.
Lemma global_field_580_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 247 snapshot = Some (Gval (Fuint 1) (global_word_26 v)))
 (initial_field : circuit_interface [::] 14 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_580 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_580 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 14 2 final = Some (Gval (Fuint 1) (global_word_580 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_580) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_14_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_580. apply global_local_580.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_580_sync.
 - exact ran.
Qed.
Lemma global_field_582_sync : field_sync_check generated_modules multiplier_instances [::14] 10 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_582_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::14] 10 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::14] 10 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_582).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_582_sync.
 - exact ran.
Qed.
Lemma global_field_582_step invalid snapshot final v initial
 (H0 : circuit_lookup [::14] 2 snapshot = Some (Gval (Fuint 1) (global_word_581 v)))
 (initial_field : circuit_interface [::14] 10 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_582 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_582 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::14] 10 2 final = Some (Gval (Fuint 1) (global_word_582 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_582) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_582. apply global_local_582.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_582_sync.
 - exact ran.
Qed.
Lemma global_field_585_sync : field_sync_check generated_modules multiplier_instances [::] 14 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_585_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 14 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 14 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_585).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_14_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_585_sync.
 - exact ran.
Qed.
Lemma global_field_585_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 249 snapshot = Some (Gval (Fuint 1) (global_word_27 v)))
 (initial_field : circuit_interface [::] 14 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_585 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_585 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 14 3 final = Some (Gval (Fuint 1) (global_word_585 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_585) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_14_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_585. apply global_local_585.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_585_sync.
 - exact ran.
Qed.
Lemma global_field_587_sync : field_sync_check generated_modules multiplier_instances [::14] 10 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_587_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::14] 10 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::14] 10 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_587).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_587_sync.
 - exact ran.
Qed.
Lemma global_field_587_step invalid snapshot final v initial
 (H0 : circuit_lookup [::14] 3 snapshot = Some (Gval (Fuint 1) (global_word_586 v)))
 (initial_field : circuit_interface [::14] 10 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_587 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_587 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::14] 10 3 final = Some (Gval (Fuint 1) (global_word_587 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_587) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_587. apply global_local_587.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_587_sync.
 - exact ran.
Qed.
Lemma global_field_601_sync : field_sync_check generated_modules multiplier_instances [::14] 11 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_601_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::14] 11 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::14] 11 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_601).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_601_sync.
 - exact ran.
Qed.
Lemma global_field_601_step invalid snapshot final v initial
 (H0 : circuit_lookup [::14] 38 snapshot = Some (Gval (Fuint 1) (global_word_600 v)))
 (initial_field : circuit_interface [::14] 11 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_601 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_601 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::14] 11 2 final = Some (Gval (Fuint 1) (global_word_601 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_601) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_601. apply global_local_601.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_601_sync.
 - exact ran.
Qed.
Lemma global_field_604_sync : field_sync_check generated_modules multiplier_instances [::] 14 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_604_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 14 5 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 14 5 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_604).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_14_5_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_604_sync.
 - exact ran.
Qed.
Lemma global_field_604_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 253 snapshot = Some (Gval (Fuint 1) (global_word_29 v)))
 (initial_field : circuit_interface [::] 14 5 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_604 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_604 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 14 5 final = Some (Gval (Fuint 1) (global_word_604 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_604) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_14_5_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_604. apply global_local_604.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_604_sync.
 - exact ran.
Qed.
Lemma global_field_607_sync : field_sync_check generated_modules multiplier_instances [::14] 11 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_607_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::14] 11 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::14] 11 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_607).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_607_sync.
 - exact ran.
Qed.
Lemma global_field_607_step invalid snapshot final v initial
 (H0 : circuit_lookup [::14] 39 snapshot = Some (Gval (Fuint 1) (global_word_606 v)))
 (initial_field : circuit_interface [::14] 11 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_607 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_607 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::14] 11 3 final = Some (Gval (Fuint 1) (global_word_607 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_607) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_607. apply global_local_607.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_607_sync.
 - exact ran.
Qed.
Lemma global_field_638_sync : field_sync_check generated_modules multiplier_instances [::] 15 6 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_638_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 15 6 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 15 6 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_638).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_15_6_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_638_sync.
 - exact ran.
Qed.
Lemma global_field_638_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 323 snapshot = Some (Gval (Fuint 1) (global_word_630 v)))
 (initial_field : circuit_interface [::] 15 6 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_638 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_638 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 15 6 final = Some (Gval (Fuint 1) (global_word_638 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_638) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_15_6_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_638. apply global_local_638.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_638_sync.
 - exact ran.
Qed.
Lemma global_field_641_sync : field_sync_check generated_modules multiplier_instances [::15] 11 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_641_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::15] 11 4 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::15] 11 4 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_641).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_641_sync.
 - exact ran.
Qed.
Lemma global_field_641_step invalid snapshot final v initial
 (H0 : circuit_lookup [::15] 40 snapshot = Some (Gval (Fuint 1) (global_word_640 v)))
 (initial_field : circuit_interface [::15] 11 4 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_641 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_641 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::15] 11 4 final = Some (Gval (Fuint 1) (global_word_641 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_641) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_641. apply global_local_641.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_641_sync.
 - exact ran.
Qed.
Lemma global_field_644_sync : field_sync_check generated_modules multiplier_instances [::] 15 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_644_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 15 4 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 15 4 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_644).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_15_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_644_sync.
 - exact ran.
Qed.
Lemma global_field_644_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 261 snapshot = Some (Gval (Fuint 1) (global_word_33 v)))
 (initial_field : circuit_interface [::] 15 4 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_644 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_644 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 15 4 final = Some (Gval (Fuint 1) (global_word_644 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_644) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_15_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_644. apply global_local_644.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_644_sync.
 - exact ran.
Qed.
Lemma global_field_646_sync : field_sync_check generated_modules multiplier_instances [::15] 10 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_646_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::15] 10 4 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::15] 10 4 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_646).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_646_sync.
 - exact ran.
Qed.
Lemma global_field_646_step invalid snapshot final v initial
 (H0 : circuit_lookup [::15] 4 snapshot = Some (Gval (Fuint 1) (global_word_645 v)))
 (initial_field : circuit_interface [::15] 10 4 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_646 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_646 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::15] 10 4 final = Some (Gval (Fuint 1) (global_word_646 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_646) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_646. apply global_local_646.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_646_sync.
 - exact ran.
Qed.
Lemma global_field_649_sync : field_sync_check generated_modules multiplier_instances [::] 15 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_649_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 15 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 15 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_649).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_15_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_649_sync.
 - exact ran.
Qed.
Lemma global_field_649_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 257 snapshot = Some (Gval (Fuint 1) (global_word_31 v)))
 (initial_field : circuit_interface [::] 15 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_649 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_649 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 15 2 final = Some (Gval (Fuint 1) (global_word_649 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_649) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_15_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_649. apply global_local_649.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_649_sync.
 - exact ran.
Qed.
Lemma global_field_651_sync : field_sync_check generated_modules multiplier_instances [::15] 10 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_651_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::15] 10 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::15] 10 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_651).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_651_sync.
 - exact ran.
Qed.
Lemma global_field_651_step invalid snapshot final v initial
 (H0 : circuit_lookup [::15] 2 snapshot = Some (Gval (Fuint 1) (global_word_650 v)))
 (initial_field : circuit_interface [::15] 10 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_651 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_651 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::15] 10 2 final = Some (Gval (Fuint 1) (global_word_651 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_651) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_651. apply global_local_651.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_651_sync.
 - exact ran.
Qed.
Lemma global_field_654_sync : field_sync_check generated_modules multiplier_instances [::] 15 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_654_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 15 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 15 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_654).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_15_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_654_sync.
 - exact ran.
Qed.
Lemma global_field_654_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 259 snapshot = Some (Gval (Fuint 1) (global_word_32 v)))
 (initial_field : circuit_interface [::] 15 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_654 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_654 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 15 3 final = Some (Gval (Fuint 1) (global_word_654 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_654) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_15_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_654. apply global_local_654.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_654_sync.
 - exact ran.
Qed.
Lemma global_field_656_sync : field_sync_check generated_modules multiplier_instances [::15] 10 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_656_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::15] 10 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::15] 10 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_656).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_656_sync.
 - exact ran.
Qed.
Lemma global_field_656_step invalid snapshot final v initial
 (H0 : circuit_lookup [::15] 3 snapshot = Some (Gval (Fuint 1) (global_word_655 v)))
 (initial_field : circuit_interface [::15] 10 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_656 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_656 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::15] 10 3 final = Some (Gval (Fuint 1) (global_word_656 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_656) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_656. apply global_local_656.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_656_sync.
 - exact ran.
Qed.
Lemma global_field_670_sync : field_sync_check generated_modules multiplier_instances [::15] 11 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_670_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::15] 11 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::15] 11 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_670).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_670_sync.
 - exact ran.
Qed.
Lemma global_field_670_step invalid snapshot final v initial
 (H0 : circuit_lookup [::15] 38 snapshot = Some (Gval (Fuint 1) (global_word_669 v)))
 (initial_field : circuit_interface [::15] 11 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_670 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_670 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::15] 11 2 final = Some (Gval (Fuint 1) (global_word_670 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_670) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_670. apply global_local_670.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_670_sync.
 - exact ran.
Qed.
Lemma global_field_673_sync : field_sync_check generated_modules multiplier_instances [::] 15 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_673_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 15 5 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 15 5 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_673).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_15_5_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_673_sync.
 - exact ran.
Qed.
Lemma global_field_673_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 263 snapshot = Some (Gval (Fuint 1) (global_word_34 v)))
 (initial_field : circuit_interface [::] 15 5 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_673 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_673 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 15 5 final = Some (Gval (Fuint 1) (global_word_673 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_673) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_15_5_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_673. apply global_local_673.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_673_sync.
 - exact ran.
Qed.
Lemma global_field_676_sync : field_sync_check generated_modules multiplier_instances [::15] 11 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_676_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::15] 11 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::15] 11 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_676).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_676_sync.
 - exact ran.
Qed.
Lemma global_field_676_step invalid snapshot final v initial
 (H0 : circuit_lookup [::15] 39 snapshot = Some (Gval (Fuint 1) (global_word_675 v)))
 (initial_field : circuit_interface [::15] 11 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_676 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_676 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::15] 11 3 final = Some (Gval (Fuint 1) (global_word_676 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_676) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_676. apply global_local_676.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_676_sync.
 - exact ran.
Qed.
Lemma global_field_707_sync : field_sync_check generated_modules multiplier_instances [::] 16 6 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_707_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 16 6 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 16 6 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_707).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_16_6_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_707_sync.
 - exact ran.
Qed.
Lemma global_field_707_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 326 snapshot = Some (Gval (Fuint 1) (global_word_699 v)))
 (initial_field : circuit_interface [::] 16 6 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_707 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_707 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 16 6 final = Some (Gval (Fuint 1) (global_word_707 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_707) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_16_6_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_707. apply global_local_707.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_707_sync.
 - exact ran.
Qed.
Lemma global_field_710_sync : field_sync_check generated_modules multiplier_instances [::16] 11 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_710_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::16] 11 4 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::16] 11 4 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_710).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_710_sync.
 - exact ran.
Qed.
Lemma global_field_710_step invalid snapshot final v initial
 (H0 : circuit_lookup [::16] 40 snapshot = Some (Gval (Fuint 1) (global_word_709 v)))
 (initial_field : circuit_interface [::16] 11 4 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_710 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_710 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::16] 11 4 final = Some (Gval (Fuint 1) (global_word_710 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_710) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_710. apply global_local_710.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_710_sync.
 - exact ran.
Qed.
Lemma global_field_713_sync : field_sync_check generated_modules multiplier_instances [::] 16 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_713_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 16 4 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 16 4 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_713).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_16_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_713_sync.
 - exact ran.
Qed.
Lemma global_field_713_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 269 snapshot = Some (Gval (Fuint 1) (global_word_37 v)))
 (initial_field : circuit_interface [::] 16 4 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_713 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_713 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 16 4 final = Some (Gval (Fuint 1) (global_word_713 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_713) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_16_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_713. apply global_local_713.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_713_sync.
 - exact ran.
Qed.
Lemma global_field_715_sync : field_sync_check generated_modules multiplier_instances [::16] 10 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_715_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::16] 10 4 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::16] 10 4 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_715).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_715_sync.
 - exact ran.
Qed.
Lemma global_field_715_step invalid snapshot final v initial
 (H0 : circuit_lookup [::16] 4 snapshot = Some (Gval (Fuint 1) (global_word_714 v)))
 (initial_field : circuit_interface [::16] 10 4 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_715 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_715 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::16] 10 4 final = Some (Gval (Fuint 1) (global_word_715 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_715) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_715. apply global_local_715.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_715_sync.
 - exact ran.
Qed.
Lemma global_field_718_sync : field_sync_check generated_modules multiplier_instances [::] 16 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_718_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 16 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 16 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_718).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_16_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_718_sync.
 - exact ran.
Qed.
Lemma global_field_718_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 265 snapshot = Some (Gval (Fuint 1) (global_word_35 v)))
 (initial_field : circuit_interface [::] 16 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_718 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_718 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 16 2 final = Some (Gval (Fuint 1) (global_word_718 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_718) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_16_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_718. apply global_local_718.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_718_sync.
 - exact ran.
Qed.
Lemma global_field_720_sync : field_sync_check generated_modules multiplier_instances [::16] 10 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_720_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::16] 10 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::16] 10 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_720).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_720_sync.
 - exact ran.
Qed.
Lemma global_field_720_step invalid snapshot final v initial
 (H0 : circuit_lookup [::16] 2 snapshot = Some (Gval (Fuint 1) (global_word_719 v)))
 (initial_field : circuit_interface [::16] 10 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_720 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_720 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::16] 10 2 final = Some (Gval (Fuint 1) (global_word_720 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_720) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_720. apply global_local_720.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_720_sync.
 - exact ran.
Qed.
Lemma global_field_723_sync : field_sync_check generated_modules multiplier_instances [::] 16 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_723_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 16 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 16 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_723).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_16_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_723_sync.
 - exact ran.
Qed.
Lemma global_field_723_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 267 snapshot = Some (Gval (Fuint 1) (global_word_36 v)))
 (initial_field : circuit_interface [::] 16 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_723 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_723 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 16 3 final = Some (Gval (Fuint 1) (global_word_723 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_723) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_16_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_723. apply global_local_723.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_723_sync.
 - exact ran.
Qed.
Lemma global_field_725_sync : field_sync_check generated_modules multiplier_instances [::16] 10 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_725_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::16] 10 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::16] 10 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_725).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_725_sync.
 - exact ran.
Qed.
Lemma global_field_725_step invalid snapshot final v initial
 (H0 : circuit_lookup [::16] 3 snapshot = Some (Gval (Fuint 1) (global_word_724 v)))
 (initial_field : circuit_interface [::16] 10 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_725 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_725 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::16] 10 3 final = Some (Gval (Fuint 1) (global_word_725 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_725) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_725. apply global_local_725.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_725_sync.
 - exact ran.
Qed.
Lemma global_field_739_sync : field_sync_check generated_modules multiplier_instances [::16] 11 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_739_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::16] 11 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::16] 11 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_739).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_739_sync.
 - exact ran.
Qed.
Lemma global_field_739_step invalid snapshot final v initial
 (H0 : circuit_lookup [::16] 38 snapshot = Some (Gval (Fuint 1) (global_word_738 v)))
 (initial_field : circuit_interface [::16] 11 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_739 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_739 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::16] 11 2 final = Some (Gval (Fuint 1) (global_word_739 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_739) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_739. apply global_local_739.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_739_sync.
 - exact ran.
Qed.
Lemma global_field_742_sync : field_sync_check generated_modules multiplier_instances [::] 16 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_742_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 16 5 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 16 5 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_742).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_16_5_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_742_sync.
 - exact ran.
Qed.
Lemma global_field_742_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 271 snapshot = Some (Gval (Fuint 1) (global_word_38 v)))
 (initial_field : circuit_interface [::] 16 5 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_742 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_742 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 16 5 final = Some (Gval (Fuint 1) (global_word_742 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_742) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_16_5_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_742. apply global_local_742.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_742_sync.
 - exact ran.
Qed.
Lemma global_field_745_sync : field_sync_check generated_modules multiplier_instances [::16] 11 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_745_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::16] 11 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::16] 11 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_745).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_745_sync.
 - exact ran.
Qed.
Lemma global_field_745_step invalid snapshot final v initial
 (H0 : circuit_lookup [::16] 39 snapshot = Some (Gval (Fuint 1) (global_word_744 v)))
 (initial_field : circuit_interface [::16] 11 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_745 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_745 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::16] 11 3 final = Some (Gval (Fuint 1) (global_word_745 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_745) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_745. apply global_local_745.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_745_sync.
 - exact ran.
Qed.
Lemma global_field_776_sync : field_sync_check generated_modules multiplier_instances [::] 17 6 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_776_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 17 6 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 17 6 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_776).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_17_6_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_776_sync.
 - exact ran.
Qed.
Lemma global_field_776_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 329 snapshot = Some (Gval (Fuint 1) (global_word_768 v)))
 (initial_field : circuit_interface [::] 17 6 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_776 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_776 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 17 6 final = Some (Gval (Fuint 1) (global_word_776 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_776) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_17_6_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_776. apply global_local_776.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_776_sync.
 - exact ran.
Qed.
Lemma global_field_779_sync : field_sync_check generated_modules multiplier_instances [::17] 11 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_779_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::17] 11 4 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::17] 11 4 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_779).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_779_sync.
 - exact ran.
Qed.
Lemma global_field_779_step invalid snapshot final v initial
 (H0 : circuit_lookup [::17] 40 snapshot = Some (Gval (Fuint 1) (global_word_778 v)))
 (initial_field : circuit_interface [::17] 11 4 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_779 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_779 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::17] 11 4 final = Some (Gval (Fuint 1) (global_word_779 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_779) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_779. apply global_local_779.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_779_sync.
 - exact ran.
Qed.
Lemma global_field_782_sync : field_sync_check generated_modules multiplier_instances [::] 17 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_782_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 17 4 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 17 4 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_782).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_17_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_782_sync.
 - exact ran.
Qed.
Lemma global_field_782_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 277 snapshot = Some (Gval (Fuint 1) (global_word_41 v)))
 (initial_field : circuit_interface [::] 17 4 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_782 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_782 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 17 4 final = Some (Gval (Fuint 1) (global_word_782 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_782) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_17_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_782. apply global_local_782.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_782_sync.
 - exact ran.
Qed.
Lemma global_field_784_sync : field_sync_check generated_modules multiplier_instances [::17] 10 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_784_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::17] 10 4 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::17] 10 4 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_784).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_784_sync.
 - exact ran.
Qed.
Lemma global_field_784_step invalid snapshot final v initial
 (H0 : circuit_lookup [::17] 4 snapshot = Some (Gval (Fuint 1) (global_word_783 v)))
 (initial_field : circuit_interface [::17] 10 4 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_784 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_784 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::17] 10 4 final = Some (Gval (Fuint 1) (global_word_784 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_784) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_784. apply global_local_784.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_784_sync.
 - exact ran.
Qed.
Lemma global_field_787_sync : field_sync_check generated_modules multiplier_instances [::] 17 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_787_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 17 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 17 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_787).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_17_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_787_sync.
 - exact ran.
Qed.
Lemma global_field_787_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 273 snapshot = Some (Gval (Fuint 1) (global_word_39 v)))
 (initial_field : circuit_interface [::] 17 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_787 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_787 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 17 2 final = Some (Gval (Fuint 1) (global_word_787 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_787) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_17_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_787. apply global_local_787.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_787_sync.
 - exact ran.
Qed.
Lemma global_field_789_sync : field_sync_check generated_modules multiplier_instances [::17] 10 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_789_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::17] 10 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::17] 10 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_789).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_789_sync.
 - exact ran.
Qed.
Lemma global_field_789_step invalid snapshot final v initial
 (H0 : circuit_lookup [::17] 2 snapshot = Some (Gval (Fuint 1) (global_word_788 v)))
 (initial_field : circuit_interface [::17] 10 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_789 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_789 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::17] 10 2 final = Some (Gval (Fuint 1) (global_word_789 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_789) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_789. apply global_local_789.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_789_sync.
 - exact ran.
Qed.
Lemma global_field_792_sync : field_sync_check generated_modules multiplier_instances [::] 17 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_792_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 17 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 17 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_792).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_17_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_792_sync.
 - exact ran.
Qed.
Lemma global_field_792_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 275 snapshot = Some (Gval (Fuint 1) (global_word_40 v)))
 (initial_field : circuit_interface [::] 17 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_792 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_792 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 17 3 final = Some (Gval (Fuint 1) (global_word_792 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_792) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_17_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_792. apply global_local_792.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_792_sync.
 - exact ran.
Qed.
Lemma global_field_794_sync : field_sync_check generated_modules multiplier_instances [::17] 10 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_794_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::17] 10 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::17] 10 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_794).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_794_sync.
 - exact ran.
Qed.
Lemma global_field_794_step invalid snapshot final v initial
 (H0 : circuit_lookup [::17] 3 snapshot = Some (Gval (Fuint 1) (global_word_793 v)))
 (initial_field : circuit_interface [::17] 10 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_794 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_794 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::17] 10 3 final = Some (Gval (Fuint 1) (global_word_794 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_794) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_794. apply global_local_794.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_794_sync.
 - exact ran.
Qed.
Lemma global_field_808_sync : field_sync_check generated_modules multiplier_instances [::17] 11 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_808_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::17] 11 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::17] 11 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_808).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_808_sync.
 - exact ran.
Qed.
Lemma global_field_808_step invalid snapshot final v initial
 (H0 : circuit_lookup [::17] 38 snapshot = Some (Gval (Fuint 1) (global_word_807 v)))
 (initial_field : circuit_interface [::17] 11 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_808 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_808 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::17] 11 2 final = Some (Gval (Fuint 1) (global_word_808 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_808) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_808. apply global_local_808.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_808_sync.
 - exact ran.
Qed.
Lemma global_field_811_sync : field_sync_check generated_modules multiplier_instances [::] 17 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_811_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 17 5 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 17 5 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_811).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_17_5_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_811_sync.
 - exact ran.
Qed.
Lemma global_field_811_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 279 snapshot = Some (Gval (Fuint 1) (global_word_42 v)))
 (initial_field : circuit_interface [::] 17 5 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_811 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_811 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 17 5 final = Some (Gval (Fuint 1) (global_word_811 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_811) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_17_5_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_811. apply global_local_811.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_811_sync.
 - exact ran.
Qed.
Lemma global_field_814_sync : field_sync_check generated_modules multiplier_instances [::17] 11 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_814_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::17] 11 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::17] 11 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_814).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_814_sync.
 - exact ran.
Qed.
Lemma global_field_814_step invalid snapshot final v initial
 (H0 : circuit_lookup [::17] 39 snapshot = Some (Gval (Fuint 1) (global_word_813 v)))
 (initial_field : circuit_interface [::17] 11 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_814 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_814 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::17] 11 3 final = Some (Gval (Fuint 1) (global_word_814 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_814) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_814. apply global_local_814.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_814_sync.
 - exact ran.
Qed.
Lemma global_field_845_sync : field_sync_check generated_modules multiplier_instances [::] 18 6 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_845_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 18 6 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 18 6 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_845).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_18_6_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_845_sync.
 - exact ran.
Qed.
Lemma global_field_845_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 332 snapshot = Some (Gval (Fuint 1) (global_word_837 v)))
 (initial_field : circuit_interface [::] 18 6 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_845 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_845 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 18 6 final = Some (Gval (Fuint 1) (global_word_845 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_845) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_18_6_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_845. apply global_local_845.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_845_sync.
 - exact ran.
Qed.
Lemma global_field_848_sync : field_sync_check generated_modules multiplier_instances [::18] 11 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_848_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::18] 11 4 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::18] 11 4 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_848).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_848_sync.
 - exact ran.
Qed.
Lemma global_field_848_step invalid snapshot final v initial
 (H0 : circuit_lookup [::18] 40 snapshot = Some (Gval (Fuint 1) (global_word_847 v)))
 (initial_field : circuit_interface [::18] 11 4 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_848 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_848 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::18] 11 4 final = Some (Gval (Fuint 1) (global_word_848 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_848) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_848. apply global_local_848.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_848_sync.
 - exact ran.
Qed.
Lemma global_field_851_sync : field_sync_check generated_modules multiplier_instances [::] 18 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_851_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 18 4 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 18 4 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_851).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_18_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_851_sync.
 - exact ran.
Qed.
Lemma global_field_851_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 285 snapshot = Some (Gval (Fuint 1) (global_word_45 v)))
 (initial_field : circuit_interface [::] 18 4 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_851 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_851 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 18 4 final = Some (Gval (Fuint 1) (global_word_851 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_851) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_18_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_851. apply global_local_851.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_851_sync.
 - exact ran.
Qed.
Lemma global_field_853_sync : field_sync_check generated_modules multiplier_instances [::18] 10 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_853_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::18] 10 4 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::18] 10 4 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_853).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_853_sync.
 - exact ran.
Qed.
Lemma global_field_853_step invalid snapshot final v initial
 (H0 : circuit_lookup [::18] 4 snapshot = Some (Gval (Fuint 1) (global_word_852 v)))
 (initial_field : circuit_interface [::18] 10 4 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_853 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_853 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::18] 10 4 final = Some (Gval (Fuint 1) (global_word_853 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_853) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_853. apply global_local_853.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_853_sync.
 - exact ran.
Qed.
Lemma global_field_856_sync : field_sync_check generated_modules multiplier_instances [::] 18 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_856_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 18 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 18 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_856).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_18_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_856_sync.
 - exact ran.
Qed.
Lemma global_field_856_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 281 snapshot = Some (Gval (Fuint 1) (global_word_43 v)))
 (initial_field : circuit_interface [::] 18 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_856 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_856 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 18 2 final = Some (Gval (Fuint 1) (global_word_856 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_856) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_18_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_856. apply global_local_856.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_856_sync.
 - exact ran.
Qed.
Lemma global_field_858_sync : field_sync_check generated_modules multiplier_instances [::18] 10 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_858_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::18] 10 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::18] 10 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_858).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_858_sync.
 - exact ran.
Qed.
Lemma global_field_858_step invalid snapshot final v initial
 (H0 : circuit_lookup [::18] 2 snapshot = Some (Gval (Fuint 1) (global_word_857 v)))
 (initial_field : circuit_interface [::18] 10 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_858 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_858 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::18] 10 2 final = Some (Gval (Fuint 1) (global_word_858 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_858) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_858. apply global_local_858.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_858_sync.
 - exact ran.
Qed.
Lemma global_field_861_sync : field_sync_check generated_modules multiplier_instances [::] 18 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_861_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 18 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 18 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_861).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_18_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_861_sync.
 - exact ran.
Qed.
Lemma global_field_861_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 283 snapshot = Some (Gval (Fuint 1) (global_word_44 v)))
 (initial_field : circuit_interface [::] 18 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_861 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_861 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 18 3 final = Some (Gval (Fuint 1) (global_word_861 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_861) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_18_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_861. apply global_local_861.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_861_sync.
 - exact ran.
Qed.
Lemma global_field_863_sync : field_sync_check generated_modules multiplier_instances [::18] 10 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_863_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::18] 10 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::18] 10 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_863).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_863_sync.
 - exact ran.
Qed.
Lemma global_field_863_step invalid snapshot final v initial
 (H0 : circuit_lookup [::18] 3 snapshot = Some (Gval (Fuint 1) (global_word_862 v)))
 (initial_field : circuit_interface [::18] 10 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_863 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_863 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::18] 10 3 final = Some (Gval (Fuint 1) (global_word_863 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_863) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_863. apply global_local_863.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_863_sync.
 - exact ran.
Qed.
Lemma global_field_877_sync : field_sync_check generated_modules multiplier_instances [::18] 11 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_877_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::18] 11 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::18] 11 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_877).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_877_sync.
 - exact ran.
Qed.
Lemma global_field_877_step invalid snapshot final v initial
 (H0 : circuit_lookup [::18] 38 snapshot = Some (Gval (Fuint 1) (global_word_876 v)))
 (initial_field : circuit_interface [::18] 11 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_877 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_877 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::18] 11 2 final = Some (Gval (Fuint 1) (global_word_877 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_877) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_877. apply global_local_877.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_877_sync.
 - exact ran.
Qed.
Lemma global_field_880_sync : field_sync_check generated_modules multiplier_instances [::] 18 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_880_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 18 5 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 18 5 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_880).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_18_5_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_880_sync.
 - exact ran.
Qed.
Lemma global_field_880_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 287 snapshot = Some (Gval (Fuint 1) (global_word_46 v)))
 (initial_field : circuit_interface [::] 18 5 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_880 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_880 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 18 5 final = Some (Gval (Fuint 1) (global_word_880 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_880) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_18_5_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_880. apply global_local_880.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_880_sync.
 - exact ran.
Qed.
Lemma global_field_883_sync : field_sync_check generated_modules multiplier_instances [::18] 11 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_883_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::18] 11 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::18] 11 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_883).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_883_sync.
 - exact ran.
Qed.
Lemma global_field_883_step invalid snapshot final v initial
 (H0 : circuit_lookup [::18] 39 snapshot = Some (Gval (Fuint 1) (global_word_882 v)))
 (initial_field : circuit_interface [::18] 11 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_883 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_883 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::18] 11 3 final = Some (Gval (Fuint 1) (global_word_883 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_883) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_883. apply global_local_883.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_883_sync.
 - exact ran.
Qed.
Lemma global_field_914_sync : field_sync_check generated_modules multiplier_instances [::] 19 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_914_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 19 4 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 19 4 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_914).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_19_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_914_sync.
 - exact ran.
Qed.
Lemma global_field_914_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 293 snapshot = Some (Gval (Fuint 1) (global_word_49 v)))
 (initial_field : circuit_interface [::] 19 4 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_914 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_914 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 19 4 final = Some (Gval (Fuint 1) (global_word_914 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_914) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_19_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_914. apply global_local_914.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_914_sync.
 - exact ran.
Qed.
Lemma global_field_917_sync : field_sync_check generated_modules multiplier_instances [::] 19 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_917_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 19 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 19 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_917).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_19_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_917_sync.
 - exact ran.
Qed.
Lemma global_field_917_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 289 snapshot = Some (Gval (Fuint 1) (global_word_47 v)))
 (initial_field : circuit_interface [::] 19 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_917 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_917 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 19 2 final = Some (Gval (Fuint 1) (global_word_917 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_917) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_19_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_917. apply global_local_917.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_917_sync.
 - exact ran.
Qed.
Lemma global_field_920_sync : field_sync_check generated_modules multiplier_instances [::] 19 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_920_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 19 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 19 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_920).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_19_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_920_sync.
 - exact ran.
Qed.
Lemma global_field_920_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 291 snapshot = Some (Gval (Fuint 1) (global_word_48 v)))
 (initial_field : circuit_interface [::] 19 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_920 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_920 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 19 3 final = Some (Gval (Fuint 1) (global_word_920 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_920) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_19_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_920. apply global_local_920.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_920_sync.
 - exact ran.
Qed.
Lemma global_field_938_sync : field_sync_check generated_modules multiplier_instances [::] 20 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_938_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 20 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 20 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_938).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_20_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_938_sync.
 - exact ran.
Qed.
Lemma global_field_938_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 295 snapshot = Some (Gval (Fuint 1) (global_word_50 v)))
 (initial_field : circuit_interface [::] 20 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_938 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_938 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 20 2 final = Some (Gval (Fuint 1) (global_word_938 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_938) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_20_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_938. apply global_local_938.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_938_sync.
 - exact ran.
Qed.
Lemma global_field_941_sync : field_sync_check generated_modules multiplier_instances [::] 20 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_941_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 20 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 20 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_941).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_20_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_941_sync.
 - exact ran.
Qed.
Lemma global_field_941_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 297 snapshot = Some (Gval (Fuint 1) (global_word_51 v)))
 (initial_field : circuit_interface [::] 20 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_941 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_941 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 20 3 final = Some (Gval (Fuint 1) (global_word_941 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_941) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_20_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_941. apply global_local_941.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_941_sync.
 - exact ran.
Qed.
Lemma global_field_956_sync : field_sync_check generated_modules multiplier_instances [::] 21 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_956_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 21 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 21 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_956).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_21_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_956_sync.
 - exact ran.
Qed.
Lemma global_field_956_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 299 snapshot = Some (Gval (Fuint 1) (global_word_52 v)))
 (initial_field : circuit_interface [::] 21 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_956 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_956 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 21 2 final = Some (Gval (Fuint 1) (global_word_956 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_956) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_21_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_956. apply global_local_956.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_956_sync.
 - exact ran.
Qed.
Lemma global_field_959_sync : field_sync_check generated_modules multiplier_instances [::] 21 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_959_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 21 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 21 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_959).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_21_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_959_sync.
 - exact ran.
Qed.
Lemma global_field_959_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 301 snapshot = Some (Gval (Fuint 1) (global_word_54 v)))
 (initial_field : circuit_interface [::] 21 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_959 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_959 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 21 3 final = Some (Gval (Fuint 1) (global_word_959 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_959) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_21_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_959. apply global_local_959.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_959_sync.
 - exact ran.
Qed.
Lemma global_field_974_sync : field_sync_check generated_modules multiplier_instances [::] 22 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_974_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 22 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 22 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_974).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_22_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_974_sync.
 - exact ran.
Qed.
Lemma global_field_974_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 307 snapshot = Some (Gval (Fuint 1) (global_word_309 v)))
 (initial_field : circuit_interface [::] 22 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_974 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_974 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 22 2 final = Some (Gval (Fuint 1) (global_word_974 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_974) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_22_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_974. apply global_local_974.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_974_sync.
 - exact ran.
Qed.
Lemma global_field_977_sync : field_sync_check generated_modules multiplier_instances [::] 22 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_977_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 22 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 22 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_977).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_22_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_977_sync.
 - exact ran.
Qed.
Lemma global_field_977_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 306 snapshot = Some (Gval (Fuint 1) (global_word_295 v)))
 (initial_field : circuit_interface [::] 22 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_977 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_977 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 22 3 final = Some (Gval (Fuint 1) (global_word_977 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_977) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_22_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_977. apply global_local_977.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_977_sync.
 - exact ran.
Qed.
Lemma global_field_992_sync : field_sync_check generated_modules multiplier_instances [::] 23 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_992_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 23 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 23 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_992).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_23_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_992_sync.
 - exact ran.
Qed.
Lemma global_field_992_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 309 snapshot = Some (Gval (Fuint 1) (global_word_333 v)))
 (initial_field : circuit_interface [::] 23 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_992 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_992 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 23 2 final = Some (Gval (Fuint 1) (global_word_992 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_992) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_23_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_992. apply global_local_992.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_992_sync.
 - exact ran.
Qed.
Lemma global_field_995_sync : field_sync_check generated_modules multiplier_instances [::] 23 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_995_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 23 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 23 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_995).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_23_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_995_sync.
 - exact ran.
Qed.
Lemma global_field_995_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 308 snapshot = Some (Gval (Fuint 1) (global_word_313 v)))
 (initial_field : circuit_interface [::] 23 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_995 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_995 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 23 3 final = Some (Gval (Fuint 1) (global_word_995 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_995) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_23_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_995. apply global_local_995.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_995_sync.
 - exact ran.
Qed.
Lemma global_field_1010_sync : field_sync_check generated_modules multiplier_instances [::] 24 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1010_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 24 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 24 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1010).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_24_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1010_sync.
 - exact ran.
Qed.
Lemma global_field_1010_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 311 snapshot = Some (Gval (Fuint 1) (global_word_357 v)))
 (initial_field : circuit_interface [::] 24 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1010 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1010 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 24 2 final = Some (Gval (Fuint 1) (global_word_1010 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1010) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_24_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1010. apply global_local_1010.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1010_sync.
 - exact ran.
Qed.
Lemma global_field_1013_sync : field_sync_check generated_modules multiplier_instances [::] 24 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1013_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 24 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 24 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1013).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_24_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1013_sync.
 - exact ran.
Qed.
Lemma global_field_1013_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 310 snapshot = Some (Gval (Fuint 1) (global_word_337 v)))
 (initial_field : circuit_interface [::] 24 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1013 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1013 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 24 3 final = Some (Gval (Fuint 1) (global_word_1013 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1013) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_24_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1013. apply global_local_1013.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1013_sync.
 - exact ran.
Qed.
Lemma global_field_1028_sync : field_sync_check generated_modules multiplier_instances [::] 25 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1028_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 25 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 25 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1028).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_25_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1028_sync.
 - exact ran.
Qed.
Lemma global_field_1028_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 313 snapshot = Some (Gval (Fuint 1) (global_word_416 v)))
 (initial_field : circuit_interface [::] 25 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1028 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1028 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 25 2 final = Some (Gval (Fuint 1) (global_word_1028 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1028) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_25_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1028. apply global_local_1028.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1028_sync.
 - exact ran.
Qed.
Lemma global_field_1031_sync : field_sync_check generated_modules multiplier_instances [::] 25 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1031_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 25 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 25 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1031).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_25_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1031_sync.
 - exact ran.
Qed.
Lemma global_field_1031_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 312 snapshot = Some (Gval (Fuint 1) (global_word_361 v)))
 (initial_field : circuit_interface [::] 25 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1031 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1031 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 25 3 final = Some (Gval (Fuint 1) (global_word_1031 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1031) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_25_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1031. apply global_local_1031.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1031_sync.
 - exact ran.
Qed.
Lemma global_field_1046_sync : field_sync_check generated_modules multiplier_instances [::] 26 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1046_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 26 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 26 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1046).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_26_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1046_sync.
 - exact ran.
Qed.
Lemma global_field_1046_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 316 snapshot = Some (Gval (Fuint 1) (global_word_485 v)))
 (initial_field : circuit_interface [::] 26 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1046 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1046 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 26 2 final = Some (Gval (Fuint 1) (global_word_1046 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1046) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_26_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1046. apply global_local_1046.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1046_sync.
 - exact ran.
Qed.
Lemma global_field_1049_sync : field_sync_check generated_modules multiplier_instances [::] 26 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1049_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 26 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 26 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1049).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_26_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1049_sync.
 - exact ran.
Qed.
Lemma global_field_1049_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 315 snapshot = Some (Gval (Fuint 1) (global_word_430 v)))
 (initial_field : circuit_interface [::] 26 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1049 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1049 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 26 3 final = Some (Gval (Fuint 1) (global_word_1049 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1049) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_26_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1049. apply global_local_1049.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1049_sync.
 - exact ran.
Qed.
Lemma global_field_1064_sync : field_sync_check generated_modules multiplier_instances [::] 27 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1064_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 27 4 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 27 4 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1064).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_27_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1064_sync.
 - exact ran.
Qed.
Lemma global_field_1064_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 318 snapshot = Some (Gval (Fuint 1) (global_word_499 v)))
 (initial_field : circuit_interface [::] 27 4 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1064 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1064 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 27 4 final = Some (Gval (Fuint 1) (global_word_1064 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1064) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_27_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1064. apply global_local_1064.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1064_sync.
 - exact ran.
Qed.
Lemma global_field_1067_sync : field_sync_check generated_modules multiplier_instances [::] 27 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1067_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 27 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 27 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1067).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_27_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1067_sync.
 - exact ran.
Qed.
Lemma global_field_1067_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 319 snapshot = Some (Gval (Fuint 1) (global_word_554 v)))
 (initial_field : circuit_interface [::] 27 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1067 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1067 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 27 2 final = Some (Gval (Fuint 1) (global_word_1067 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1067) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_27_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1067. apply global_local_1067.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1067_sync.
 - exact ran.
Qed.
Lemma global_field_1070_sync : field_sync_check generated_modules multiplier_instances [::] 27 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1070_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 27 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 27 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1070).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_27_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1070_sync.
 - exact ran.
Qed.
Lemma global_field_1070_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 245 snapshot = Some (Gval (Fuint 1) (global_word_25 v)))
 (initial_field : circuit_interface [::] 27 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1070 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1070 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 27 3 final = Some (Gval (Fuint 1) (global_word_1070 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1070) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_27_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1070. apply global_local_1070.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1070_sync.
 - exact ran.
Qed.
Lemma global_field_1088_sync : field_sync_check generated_modules multiplier_instances [::] 28 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1088_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 28 4 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 28 4 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1088).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_28_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1088_sync.
 - exact ran.
Qed.
Lemma global_field_1088_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 321 snapshot = Some (Gval (Fuint 1) (global_word_568 v)))
 (initial_field : circuit_interface [::] 28 4 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1088 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1088 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 28 4 final = Some (Gval (Fuint 1) (global_word_1088 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1088) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_28_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1088. apply global_local_1088.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1088_sync.
 - exact ran.
Qed.
Lemma global_field_1091_sync : field_sync_check generated_modules multiplier_instances [::] 28 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1091_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 28 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 28 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1091).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_28_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1091_sync.
 - exact ran.
Qed.
Lemma global_field_1091_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 322 snapshot = Some (Gval (Fuint 1) (global_word_623 v)))
 (initial_field : circuit_interface [::] 28 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1091 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1091 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 28 2 final = Some (Gval (Fuint 1) (global_word_1091 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1091) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_28_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1091. apply global_local_1091.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1091_sync.
 - exact ran.
Qed.
Lemma global_field_1094_sync : field_sync_check generated_modules multiplier_instances [::] 28 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1094_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 28 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 28 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1094).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_28_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1094_sync.
 - exact ran.
Qed.
Lemma global_field_1094_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 255 snapshot = Some (Gval (Fuint 1) (global_word_30 v)))
 (initial_field : circuit_interface [::] 28 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1094 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1094 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 28 3 final = Some (Gval (Fuint 1) (global_word_1094 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1094) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_28_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1094. apply global_local_1094.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1094_sync.
 - exact ran.
Qed.
Lemma global_field_1112_sync : field_sync_check generated_modules multiplier_instances [::] 29 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1112_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 29 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 29 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1112).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_29_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1112_sync.
 - exact ran.
Qed.
Lemma global_field_1112_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 325 snapshot = Some (Gval (Fuint 1) (global_word_692 v)))
 (initial_field : circuit_interface [::] 29 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1112 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1112 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 29 2 final = Some (Gval (Fuint 1) (global_word_1112 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1112) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_29_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1112. apply global_local_1112.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1112_sync.
 - exact ran.
Qed.
Lemma global_field_1115_sync : field_sync_check generated_modules multiplier_instances [::] 29 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1115_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 29 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 29 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1115).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_29_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1115_sync.
 - exact ran.
Qed.
Lemma global_field_1115_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 324 snapshot = Some (Gval (Fuint 1) (global_word_637 v)))
 (initial_field : circuit_interface [::] 29 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1115 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1115 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 29 3 final = Some (Gval (Fuint 1) (global_word_1115 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1115) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_29_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1115. apply global_local_1115.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1115_sync.
 - exact ran.
Qed.
Lemma global_field_1130_sync : field_sync_check generated_modules multiplier_instances [::] 30 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1130_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 30 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 30 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1130).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_30_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1130_sync.
 - exact ran.
Qed.
Lemma global_field_1130_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 328 snapshot = Some (Gval (Fuint 1) (global_word_761 v)))
 (initial_field : circuit_interface [::] 30 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1130 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1130 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 30 2 final = Some (Gval (Fuint 1) (global_word_1130 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1130) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_30_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1130. apply global_local_1130.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1130_sync.
 - exact ran.
Qed.
Lemma global_field_1133_sync : field_sync_check generated_modules multiplier_instances [::] 30 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1133_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 30 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 30 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1133).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_30_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1133_sync.
 - exact ran.
Qed.
Lemma global_field_1133_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 327 snapshot = Some (Gval (Fuint 1) (global_word_706 v)))
 (initial_field : circuit_interface [::] 30 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1133 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1133 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 30 3 final = Some (Gval (Fuint 1) (global_word_1133 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1133) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_30_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1133. apply global_local_1133.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1133_sync.
 - exact ran.
Qed.
Lemma global_field_1148_sync : field_sync_check generated_modules multiplier_instances [::] 31 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1148_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 31 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 31 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1148).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_31_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1148_sync.
 - exact ran.
Qed.
Lemma global_field_1148_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 331 snapshot = Some (Gval (Fuint 1) (global_word_830 v)))
 (initial_field : circuit_interface [::] 31 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1148 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1148 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 31 2 final = Some (Gval (Fuint 1) (global_word_1148 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1148) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_31_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1148. apply global_local_1148.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1148_sync.
 - exact ran.
Qed.
Lemma global_field_1151_sync : field_sync_check generated_modules multiplier_instances [::] 31 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1151_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 31 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 31 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1151).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_31_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1151_sync.
 - exact ran.
Qed.
Lemma global_field_1151_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 330 snapshot = Some (Gval (Fuint 1) (global_word_775 v)))
 (initial_field : circuit_interface [::] 31 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1151 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1151 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 31 3 final = Some (Gval (Fuint 1) (global_word_1151 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1151) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_31_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1151. apply global_local_1151.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1151_sync.
 - exact ran.
Qed.
Lemma global_field_1166_sync : field_sync_check generated_modules multiplier_instances [::] 32 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1166_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 32 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 32 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1166).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_32_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1166_sync.
 - exact ran.
Qed.
Lemma global_field_1166_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 334 snapshot = Some (Gval (Fuint 1) (global_word_899 v)))
 (initial_field : circuit_interface [::] 32 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1166 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1166 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 32 2 final = Some (Gval (Fuint 1) (global_word_1166 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1166) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_32_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1166. apply global_local_1166.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1166_sync.
 - exact ran.
Qed.
Lemma global_field_1169_sync : field_sync_check generated_modules multiplier_instances [::] 32 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1169_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 32 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 32 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1169).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_32_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1169_sync.
 - exact ran.
Qed.
Lemma global_field_1169_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 333 snapshot = Some (Gval (Fuint 1) (global_word_844 v)))
 (initial_field : circuit_interface [::] 32 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1169 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1169 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 32 3 final = Some (Gval (Fuint 1) (global_word_1169 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1169) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_32_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1169. apply global_local_1169.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1169_sync.
 - exact ran.
Qed.
Lemma global_field_1184_sync : field_sync_check generated_modules multiplier_instances [::] 33 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1184_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 33 4 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 33 4 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1184).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_33_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1184_sync.
 - exact ran.
Qed.
Lemma global_field_1184_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 336 snapshot = Some (Gval (Fuint 1) (global_word_913 v)))
 (initial_field : circuit_interface [::] 33 4 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1184 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1184 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 33 4 final = Some (Gval (Fuint 1) (global_word_1184 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1184) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_33_4_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1184. apply global_local_1184.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1184_sync.
 - exact ran.
Qed.
Lemma global_field_1187_sync : field_sync_check generated_modules multiplier_instances [::] 33 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1187_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 33 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 33 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1187).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_33_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1187_sync.
 - exact ran.
Qed.
Lemma global_field_1187_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 337 snapshot = Some (Gval (Fuint 1) (global_word_933 v)))
 (initial_field : circuit_interface [::] 33 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1187 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1187 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 33 2 final = Some (Gval (Fuint 1) (global_word_1187 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1187) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_33_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1187. apply global_local_1187.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1187_sync.
 - exact ran.
Qed.
Lemma global_field_1190_sync : field_sync_check generated_modules multiplier_instances [::] 33 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1190_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 33 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 33 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1190).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_33_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1190_sync.
 - exact ran.
Qed.
Lemma global_field_1190_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 335 snapshot = Some (Gval (Fuint 1) (global_word_906 v)))
 (initial_field : circuit_interface [::] 33 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1190 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1190 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 33 3 final = Some (Gval (Fuint 1) (global_word_1190 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1190) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_33_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1190. apply global_local_1190.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1190_sync.
 - exact ran.
Qed.
Lemma global_field_1208_sync : field_sync_check generated_modules multiplier_instances [::] 34 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1208_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 34 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 34 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1208).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_34_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1208_sync.
 - exact ran.
Qed.
Lemma global_field_1208_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 339 snapshot = Some (Gval (Fuint 1) (global_word_951 v)))
 (initial_field : circuit_interface [::] 34 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1208 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1208 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 34 2 final = Some (Gval (Fuint 1) (global_word_1208 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1208) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_34_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1208. apply global_local_1208.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1208_sync.
 - exact ran.
Qed.
Lemma global_field_1211_sync : field_sync_check generated_modules multiplier_instances [::] 34 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1211_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 34 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 34 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1211).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_34_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1211_sync.
 - exact ran.
Qed.
Lemma global_field_1211_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 338 snapshot = Some (Gval (Fuint 1) (global_word_937 v)))
 (initial_field : circuit_interface [::] 34 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1211 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1211 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 34 3 final = Some (Gval (Fuint 1) (global_word_1211 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1211) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_34_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1211. apply global_local_1211.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1211_sync.
 - exact ran.
Qed.
Lemma global_field_1226_sync : field_sync_check generated_modules multiplier_instances [::] 35 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1226_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 35 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 35 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1226).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_35_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1226_sync.
 - exact ran.
Qed.
Lemma global_field_1226_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 341 snapshot = Some (Gval (Fuint 1) (global_word_969 v)))
 (initial_field : circuit_interface [::] 35 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1226 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1226 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 35 2 final = Some (Gval (Fuint 1) (global_word_1226 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1226) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_35_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1226. apply global_local_1226.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1226_sync.
 - exact ran.
Qed.
Lemma global_field_1229_sync : field_sync_check generated_modules multiplier_instances [::] 35 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1229_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 35 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 35 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1229).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_35_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1229_sync.
 - exact ran.
Qed.
Lemma global_field_1229_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 340 snapshot = Some (Gval (Fuint 1) (global_word_955 v)))
 (initial_field : circuit_interface [::] 35 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1229 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1229 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 35 3 final = Some (Gval (Fuint 1) (global_word_1229 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1229) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_35_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1229. apply global_local_1229.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1229_sync.
 - exact ran.
Qed.
Lemma global_field_1244_sync : field_sync_check generated_modules multiplier_instances [::] 36 2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1244_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 36 2 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 36 2 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1244).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_36_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1244_sync.
 - exact ran.
Qed.
Lemma global_field_1244_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 303 snapshot = Some (Gval (Fuint 1) (global_word_55 v)))
 (initial_field : circuit_interface [::] 36 2 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1244 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1244 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 36 2 final = Some (Gval (Fuint 1) (global_word_1244 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1244) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_36_2_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1244. apply global_local_1244.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1244_sync.
 - exact ran.
Qed.
Lemma global_field_1247_sync : field_sync_check generated_modules multiplier_instances [::] 36 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1247_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 36 3 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 36 3 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1247).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_36_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1247_sync.
 - exact ran.
Qed.
Lemma global_field_1247_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 342 snapshot = Some (Gval (Fuint 1) (global_word_973 v)))
 (initial_field : circuit_interface [::] 36 3 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1247 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1247 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 36 3 final = Some (Gval (Fuint 1) (global_word_1247 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1247) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_36_3_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1247. apply global_local_1247.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1247_sync.
 - exact ran.
Qed.
Lemma global_field_1310_sync : field_sync_check generated_modules multiplier_instances [::] 7 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1310_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 7 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 7 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1310).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_7_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1310_sync.
 - exact ran.
Qed.
Lemma global_field_1310_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 0 snapshot = Some (Gval Fclock (global_word_0 v)))
 (initial_field : circuit_interface [::] 7 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1310 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1310 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 7 0 final = Some (Gval Fclock (global_word_1310 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1310) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_7_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1310. apply global_local_1310.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1310_sync.
 - exact ran.
Qed.
Lemma global_field_1311_sync : field_sync_check generated_modules multiplier_instances [::] 7 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1311_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 7 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 7 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1311).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_7_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1311_sync.
 - exact ran.
Qed.
Lemma global_field_1311_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 1 snapshot = Some (Gval (Fuint 1) (global_word_1 v)))
 (initial_field : circuit_interface [::] 7 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1311 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1311 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 7 1 final = Some (Gval (Fuint 1) (global_word_1311 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1311) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_7_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1311. apply global_local_1311.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1311_sync.
 - exact ran.
Qed.
Lemma global_field_1312_sync : field_sync_check generated_modules multiplier_instances [::] 8 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1312_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 8 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 8 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1312).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_8_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1312_sync.
 - exact ran.
Qed.
Lemma global_field_1312_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 0 snapshot = Some (Gval Fclock (global_word_0 v)))
 (initial_field : circuit_interface [::] 8 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1312 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1312 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 8 0 final = Some (Gval Fclock (global_word_1312 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1312) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_8_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1312. apply global_local_1312.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1312_sync.
 - exact ran.
Qed.
Lemma global_field_1313_sync : field_sync_check generated_modules multiplier_instances [::] 8 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1313_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 8 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 8 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1313).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_8_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1313_sync.
 - exact ran.
Qed.
Lemma global_field_1313_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 1 snapshot = Some (Gval (Fuint 1) (global_word_1 v)))
 (initial_field : circuit_interface [::] 8 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1313 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1313 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 8 1 final = Some (Gval (Fuint 1) (global_word_1313 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1313) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_8_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1313. apply global_local_1313.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1313_sync.
 - exact ran.
Qed.
Lemma global_field_1314_sync : field_sync_check generated_modules multiplier_instances [::] 9 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1314_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 9 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 9 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1314).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_9_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1314_sync.
 - exact ran.
Qed.
Lemma global_field_1314_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 0 snapshot = Some (Gval Fclock (global_word_0 v)))
 (initial_field : circuit_interface [::] 9 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1314 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1314 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 9 0 final = Some (Gval Fclock (global_word_1314 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1314) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_9_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1314. apply global_local_1314.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1314_sync.
 - exact ran.
Qed.
Lemma global_field_1315_sync : field_sync_check generated_modules multiplier_instances [::] 9 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1315_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 9 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 9 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1315).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_9_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1315_sync.
 - exact ran.
Qed.
Lemma global_field_1315_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 1 snapshot = Some (Gval (Fuint 1) (global_word_1 v)))
 (initial_field : circuit_interface [::] 9 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1315 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1315 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 9 1 final = Some (Gval (Fuint 1) (global_word_1315 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1315) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_9_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1315. apply global_local_1315.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1315_sync.
 - exact ran.
Qed.
Lemma global_field_1316_sync : field_sync_check generated_modules multiplier_instances [::] 10 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1316_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 10 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 10 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1316).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_10_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1316_sync.
 - exact ran.
Qed.
Lemma global_field_1316_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 0 snapshot = Some (Gval Fclock (global_word_0 v)))
 (initial_field : circuit_interface [::] 10 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1316 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1316 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 10 0 final = Some (Gval Fclock (global_word_1316 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1316) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_10_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1316. apply global_local_1316.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1316_sync.
 - exact ran.
Qed.
Lemma global_field_1317_sync : field_sync_check generated_modules multiplier_instances [::] 10 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1317_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 10 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 10 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1317).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_10_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1317_sync.
 - exact ran.
Qed.
Lemma global_field_1317_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 1 snapshot = Some (Gval (Fuint 1) (global_word_1 v)))
 (initial_field : circuit_interface [::] 10 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1317 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1317 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 10 1 final = Some (Gval (Fuint 1) (global_word_1317 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1317) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_10_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1317. apply global_local_1317.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1317_sync.
 - exact ran.
Qed.
Lemma global_field_1318_sync : field_sync_check generated_modules multiplier_instances [::] 11 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1318_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 11 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 11 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1318).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_11_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1318_sync.
 - exact ran.
Qed.
Lemma global_field_1318_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 0 snapshot = Some (Gval Fclock (global_word_0 v)))
 (initial_field : circuit_interface [::] 11 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1318 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1318 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 11 0 final = Some (Gval Fclock (global_word_1318 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1318) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_11_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1318. apply global_local_1318.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1318_sync.
 - exact ran.
Qed.
Lemma global_field_1319_sync : field_sync_check generated_modules multiplier_instances [::] 11 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1319_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 11 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 11 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1319).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_11_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1319_sync.
 - exact ran.
Qed.
Lemma global_field_1319_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 1 snapshot = Some (Gval (Fuint 1) (global_word_1 v)))
 (initial_field : circuit_interface [::] 11 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1319 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1319 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 11 1 final = Some (Gval (Fuint 1) (global_word_1319 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1319) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_11_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1319. apply global_local_1319.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1319_sync.
 - exact ran.
Qed.
Lemma global_field_1320_sync : field_sync_check generated_modules multiplier_instances [::] 12 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1320_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 12 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 12 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1320).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_12_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1320_sync.
 - exact ran.
Qed.
Lemma global_field_1320_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 0 snapshot = Some (Gval Fclock (global_word_0 v)))
 (initial_field : circuit_interface [::] 12 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1320 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1320 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 12 0 final = Some (Gval Fclock (global_word_1320 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1320) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_12_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1320. apply global_local_1320.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1320_sync.
 - exact ran.
Qed.
Lemma global_field_1321_sync : field_sync_check generated_modules multiplier_instances [::] 12 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1321_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 12 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 12 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1321).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_12_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1321_sync.
 - exact ran.
Qed.
Lemma global_field_1321_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 1 snapshot = Some (Gval (Fuint 1) (global_word_1 v)))
 (initial_field : circuit_interface [::] 12 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1321 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1321 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 12 1 final = Some (Gval (Fuint 1) (global_word_1321 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1321) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_12_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1321. apply global_local_1321.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1321_sync.
 - exact ran.
Qed.
Lemma global_field_1322_sync : field_sync_check generated_modules multiplier_instances [::] 13 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1322_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 13 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 13 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1322).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_13_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1322_sync.
 - exact ran.
Qed.
Lemma global_field_1322_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 0 snapshot = Some (Gval Fclock (global_word_0 v)))
 (initial_field : circuit_interface [::] 13 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1322 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1322 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 13 0 final = Some (Gval Fclock (global_word_1322 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1322) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_13_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1322. apply global_local_1322.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1322_sync.
 - exact ran.
Qed.
Lemma global_field_1323_sync : field_sync_check generated_modules multiplier_instances [::] 13 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1323_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 13 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 13 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1323).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_13_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1323_sync.
 - exact ran.
Qed.
Lemma global_field_1323_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 1 snapshot = Some (Gval (Fuint 1) (global_word_1 v)))
 (initial_field : circuit_interface [::] 13 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1323 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1323 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 13 1 final = Some (Gval (Fuint 1) (global_word_1323 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1323) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_13_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1323. apply global_local_1323.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1323_sync.
 - exact ran.
Qed.
Lemma global_field_1324_sync : field_sync_check generated_modules multiplier_instances [::] 14 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1324_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 14 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 14 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1324).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_14_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1324_sync.
 - exact ran.
Qed.
Lemma global_field_1324_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 0 snapshot = Some (Gval Fclock (global_word_0 v)))
 (initial_field : circuit_interface [::] 14 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1324 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1324 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 14 0 final = Some (Gval Fclock (global_word_1324 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1324) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_14_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1324. apply global_local_1324.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1324_sync.
 - exact ran.
Qed.
Lemma global_field_1325_sync : field_sync_check generated_modules multiplier_instances [::] 14 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1325_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 14 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 14 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1325).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_14_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1325_sync.
 - exact ran.
Qed.
Lemma global_field_1325_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 1 snapshot = Some (Gval (Fuint 1) (global_word_1 v)))
 (initial_field : circuit_interface [::] 14 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1325 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1325 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 14 1 final = Some (Gval (Fuint 1) (global_word_1325 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1325) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_14_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1325. apply global_local_1325.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1325_sync.
 - exact ran.
Qed.
Lemma global_field_1326_sync : field_sync_check generated_modules multiplier_instances [::] 15 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1326_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 15 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 15 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1326).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_15_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1326_sync.
 - exact ran.
Qed.
Lemma global_field_1326_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 0 snapshot = Some (Gval Fclock (global_word_0 v)))
 (initial_field : circuit_interface [::] 15 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1326 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1326 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 15 0 final = Some (Gval Fclock (global_word_1326 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1326) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_15_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1326. apply global_local_1326.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1326_sync.
 - exact ran.
Qed.
Lemma global_field_1327_sync : field_sync_check generated_modules multiplier_instances [::] 15 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1327_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 15 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 15 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1327).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_15_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1327_sync.
 - exact ran.
Qed.
Lemma global_field_1327_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 1 snapshot = Some (Gval (Fuint 1) (global_word_1 v)))
 (initial_field : circuit_interface [::] 15 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1327 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1327 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 15 1 final = Some (Gval (Fuint 1) (global_word_1327 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1327) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_15_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1327. apply global_local_1327.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1327_sync.
 - exact ran.
Qed.
Lemma global_field_1328_sync : field_sync_check generated_modules multiplier_instances [::] 16 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1328_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 16 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 16 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1328).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_16_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1328_sync.
 - exact ran.
Qed.
Lemma global_field_1328_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 0 snapshot = Some (Gval Fclock (global_word_0 v)))
 (initial_field : circuit_interface [::] 16 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1328 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1328 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 16 0 final = Some (Gval Fclock (global_word_1328 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1328) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_16_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1328. apply global_local_1328.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1328_sync.
 - exact ran.
Qed.
Lemma global_field_1329_sync : field_sync_check generated_modules multiplier_instances [::] 16 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1329_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 16 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 16 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1329).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_16_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1329_sync.
 - exact ran.
Qed.
Lemma global_field_1329_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 1 snapshot = Some (Gval (Fuint 1) (global_word_1 v)))
 (initial_field : circuit_interface [::] 16 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1329 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1329 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 16 1 final = Some (Gval (Fuint 1) (global_word_1329 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1329) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_16_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1329. apply global_local_1329.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1329_sync.
 - exact ran.
Qed.
Lemma global_field_1330_sync : field_sync_check generated_modules multiplier_instances [::] 17 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1330_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 17 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 17 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1330).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_17_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1330_sync.
 - exact ran.
Qed.
Lemma global_field_1330_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 0 snapshot = Some (Gval Fclock (global_word_0 v)))
 (initial_field : circuit_interface [::] 17 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1330 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1330 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 17 0 final = Some (Gval Fclock (global_word_1330 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1330) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_17_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1330. apply global_local_1330.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1330_sync.
 - exact ran.
Qed.
Lemma global_field_1331_sync : field_sync_check generated_modules multiplier_instances [::] 17 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1331_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 17 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 17 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1331).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_17_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1331_sync.
 - exact ran.
Qed.
Lemma global_field_1331_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 1 snapshot = Some (Gval (Fuint 1) (global_word_1 v)))
 (initial_field : circuit_interface [::] 17 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1331 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1331 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 17 1 final = Some (Gval (Fuint 1) (global_word_1331 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1331) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_17_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1331. apply global_local_1331.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1331_sync.
 - exact ran.
Qed.
Lemma global_field_1332_sync : field_sync_check generated_modules multiplier_instances [::] 18 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1332_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 18 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 18 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1332).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_18_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1332_sync.
 - exact ran.
Qed.
Lemma global_field_1332_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 0 snapshot = Some (Gval Fclock (global_word_0 v)))
 (initial_field : circuit_interface [::] 18 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1332 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1332 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 18 0 final = Some (Gval Fclock (global_word_1332 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1332) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_18_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1332. apply global_local_1332.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1332_sync.
 - exact ran.
Qed.
Lemma global_field_1333_sync : field_sync_check generated_modules multiplier_instances [::] 18 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1333_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 18 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 18 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1333).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_18_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1333_sync.
 - exact ran.
Qed.
Lemma global_field_1333_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 1 snapshot = Some (Gval (Fuint 1) (global_word_1 v)))
 (initial_field : circuit_interface [::] 18 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1333 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1333 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 18 1 final = Some (Gval (Fuint 1) (global_word_1333 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1333) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_18_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1333. apply global_local_1333.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1333_sync.
 - exact ran.
Qed.
Lemma global_field_1334_sync : field_sync_check generated_modules multiplier_instances [::] 19 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1334_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 19 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 19 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1334).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_19_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1334_sync.
 - exact ran.
Qed.
Lemma global_field_1334_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 0 snapshot = Some (Gval Fclock (global_word_0 v)))
 (initial_field : circuit_interface [::] 19 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1334 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1334 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 19 0 final = Some (Gval Fclock (global_word_1334 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1334) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_19_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1334. apply global_local_1334.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1334_sync.
 - exact ran.
Qed.
Lemma global_field_1335_sync : field_sync_check generated_modules multiplier_instances [::] 19 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1335_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 19 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 19 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1335).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_19_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1335_sync.
 - exact ran.
Qed.
Lemma global_field_1335_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 1 snapshot = Some (Gval (Fuint 1) (global_word_1 v)))
 (initial_field : circuit_interface [::] 19 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1335 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1335 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 19 1 final = Some (Gval (Fuint 1) (global_word_1335 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1335) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_19_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1335. apply global_local_1335.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1335_sync.
 - exact ran.
Qed.
Lemma global_field_1336_sync : field_sync_check generated_modules multiplier_instances [::] 20 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1336_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 20 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 20 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1336).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_20_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1336_sync.
 - exact ran.
Qed.
Lemma global_field_1336_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 0 snapshot = Some (Gval Fclock (global_word_0 v)))
 (initial_field : circuit_interface [::] 20 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1336 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1336 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 20 0 final = Some (Gval Fclock (global_word_1336 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1336) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_20_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1336. apply global_local_1336.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1336_sync.
 - exact ran.
Qed.
Lemma global_field_1337_sync : field_sync_check generated_modules multiplier_instances [::] 20 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1337_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 20 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 20 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1337).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_20_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1337_sync.
 - exact ran.
Qed.
Lemma global_field_1337_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 1 snapshot = Some (Gval (Fuint 1) (global_word_1 v)))
 (initial_field : circuit_interface [::] 20 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1337 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1337 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 20 1 final = Some (Gval (Fuint 1) (global_word_1337 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1337) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_20_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1337. apply global_local_1337.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1337_sync.
 - exact ran.
Qed.
Lemma global_field_1338_sync : field_sync_check generated_modules multiplier_instances [::] 21 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1338_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 21 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 21 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1338).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_21_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1338_sync.
 - exact ran.
Qed.
Lemma global_field_1338_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 0 snapshot = Some (Gval Fclock (global_word_0 v)))
 (initial_field : circuit_interface [::] 21 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1338 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1338 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 21 0 final = Some (Gval Fclock (global_word_1338 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1338) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_21_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1338. apply global_local_1338.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1338_sync.
 - exact ran.
Qed.
Lemma global_field_1339_sync : field_sync_check generated_modules multiplier_instances [::] 21 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1339_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 21 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 21 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1339).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_21_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1339_sync.
 - exact ran.
Qed.
Lemma global_field_1339_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 1 snapshot = Some (Gval (Fuint 1) (global_word_1 v)))
 (initial_field : circuit_interface [::] 21 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1339 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1339 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 21 1 final = Some (Gval (Fuint 1) (global_word_1339 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1339) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_21_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1339. apply global_local_1339.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1339_sync.
 - exact ran.
Qed.
Lemma global_field_1340_sync : field_sync_check generated_modules multiplier_instances [::] 22 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1340_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 22 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 22 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1340).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_22_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1340_sync.
 - exact ran.
Qed.
Lemma global_field_1340_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 0 snapshot = Some (Gval Fclock (global_word_0 v)))
 (initial_field : circuit_interface [::] 22 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1340 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1340 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 22 0 final = Some (Gval Fclock (global_word_1340 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1340) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_22_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1340. apply global_local_1340.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1340_sync.
 - exact ran.
Qed.
Lemma global_field_1341_sync : field_sync_check generated_modules multiplier_instances [::] 22 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1341_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 22 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 22 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1341).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_22_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1341_sync.
 - exact ran.
Qed.
Lemma global_field_1341_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 1 snapshot = Some (Gval (Fuint 1) (global_word_1 v)))
 (initial_field : circuit_interface [::] 22 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1341 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1341 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 22 1 final = Some (Gval (Fuint 1) (global_word_1341 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1341) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_22_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1341. apply global_local_1341.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1341_sync.
 - exact ran.
Qed.
Lemma global_field_1342_sync : field_sync_check generated_modules multiplier_instances [::] 23 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1342_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 23 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 23 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1342).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_23_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1342_sync.
 - exact ran.
Qed.
Lemma global_field_1342_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 0 snapshot = Some (Gval Fclock (global_word_0 v)))
 (initial_field : circuit_interface [::] 23 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1342 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1342 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 23 0 final = Some (Gval Fclock (global_word_1342 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1342) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_23_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1342. apply global_local_1342.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1342_sync.
 - exact ran.
Qed.
Lemma global_field_1343_sync : field_sync_check generated_modules multiplier_instances [::] 23 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1343_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 23 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 23 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1343).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_23_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1343_sync.
 - exact ran.
Qed.
Lemma global_field_1343_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 1 snapshot = Some (Gval (Fuint 1) (global_word_1 v)))
 (initial_field : circuit_interface [::] 23 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1343 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1343 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 23 1 final = Some (Gval (Fuint 1) (global_word_1343 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1343) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_23_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1343. apply global_local_1343.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1343_sync.
 - exact ran.
Qed.
Lemma global_field_1344_sync : field_sync_check generated_modules multiplier_instances [::] 24 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1344_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 24 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 24 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1344).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_24_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1344_sync.
 - exact ran.
Qed.
Lemma global_field_1344_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 0 snapshot = Some (Gval Fclock (global_word_0 v)))
 (initial_field : circuit_interface [::] 24 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1344 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1344 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 24 0 final = Some (Gval Fclock (global_word_1344 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1344) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_24_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1344. apply global_local_1344.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1344_sync.
 - exact ran.
Qed.
Lemma global_field_1345_sync : field_sync_check generated_modules multiplier_instances [::] 24 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1345_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 24 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 24 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1345).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_24_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1345_sync.
 - exact ran.
Qed.
Lemma global_field_1345_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 1 snapshot = Some (Gval (Fuint 1) (global_word_1 v)))
 (initial_field : circuit_interface [::] 24 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1345 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1345 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 24 1 final = Some (Gval (Fuint 1) (global_word_1345 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1345) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_24_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1345. apply global_local_1345.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1345_sync.
 - exact ran.
Qed.
Lemma global_field_1346_sync : field_sync_check generated_modules multiplier_instances [::] 25 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1346_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 25 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 25 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1346).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_25_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1346_sync.
 - exact ran.
Qed.
Lemma global_field_1346_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 0 snapshot = Some (Gval Fclock (global_word_0 v)))
 (initial_field : circuit_interface [::] 25 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1346 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1346 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 25 0 final = Some (Gval Fclock (global_word_1346 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1346) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_25_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1346. apply global_local_1346.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1346_sync.
 - exact ran.
Qed.
Lemma global_field_1347_sync : field_sync_check generated_modules multiplier_instances [::] 25 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1347_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 25 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 25 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1347).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_25_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1347_sync.
 - exact ran.
Qed.
Lemma global_field_1347_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 1 snapshot = Some (Gval (Fuint 1) (global_word_1 v)))
 (initial_field : circuit_interface [::] 25 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1347 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1347 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 25 1 final = Some (Gval (Fuint 1) (global_word_1347 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1347) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_25_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1347. apply global_local_1347.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1347_sync.
 - exact ran.
Qed.
Lemma global_field_1348_sync : field_sync_check generated_modules multiplier_instances [::] 26 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1348_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 26 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 26 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1348).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_26_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1348_sync.
 - exact ran.
Qed.
Lemma global_field_1348_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 0 snapshot = Some (Gval Fclock (global_word_0 v)))
 (initial_field : circuit_interface [::] 26 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1348 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1348 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 26 0 final = Some (Gval Fclock (global_word_1348 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1348) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_26_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1348. apply global_local_1348.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1348_sync.
 - exact ran.
Qed.
Lemma global_field_1349_sync : field_sync_check generated_modules multiplier_instances [::] 26 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1349_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 26 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 26 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1349).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_26_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1349_sync.
 - exact ran.
Qed.
Lemma global_field_1349_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 1 snapshot = Some (Gval (Fuint 1) (global_word_1 v)))
 (initial_field : circuit_interface [::] 26 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1349 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1349 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 26 1 final = Some (Gval (Fuint 1) (global_word_1349 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1349) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_26_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1349. apply global_local_1349.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1349_sync.
 - exact ran.
Qed.
Lemma global_field_1350_sync : field_sync_check generated_modules multiplier_instances [::] 27 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1350_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 27 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 27 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1350).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_27_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1350_sync.
 - exact ran.
Qed.
Lemma global_field_1350_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 0 snapshot = Some (Gval Fclock (global_word_0 v)))
 (initial_field : circuit_interface [::] 27 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1350 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1350 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 27 0 final = Some (Gval Fclock (global_word_1350 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1350) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_27_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1350. apply global_local_1350.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1350_sync.
 - exact ran.
Qed.
Lemma global_field_1351_sync : field_sync_check generated_modules multiplier_instances [::] 27 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1351_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 27 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 27 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1351).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_27_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1351_sync.
 - exact ran.
Qed.
Lemma global_field_1351_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 1 snapshot = Some (Gval (Fuint 1) (global_word_1 v)))
 (initial_field : circuit_interface [::] 27 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1351 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1351 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 27 1 final = Some (Gval (Fuint 1) (global_word_1351 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1351) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_27_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1351. apply global_local_1351.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1351_sync.
 - exact ran.
Qed.
Lemma global_field_1352_sync : field_sync_check generated_modules multiplier_instances [::] 28 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1352_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 28 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 28 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1352).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_28_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1352_sync.
 - exact ran.
Qed.
Lemma global_field_1352_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 0 snapshot = Some (Gval Fclock (global_word_0 v)))
 (initial_field : circuit_interface [::] 28 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1352 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1352 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 28 0 final = Some (Gval Fclock (global_word_1352 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1352) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_28_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1352. apply global_local_1352.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1352_sync.
 - exact ran.
Qed.
Lemma global_field_1353_sync : field_sync_check generated_modules multiplier_instances [::] 28 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1353_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 28 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 28 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1353).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_28_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1353_sync.
 - exact ran.
Qed.
Lemma global_field_1353_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 1 snapshot = Some (Gval (Fuint 1) (global_word_1 v)))
 (initial_field : circuit_interface [::] 28 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1353 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1353 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 28 1 final = Some (Gval (Fuint 1) (global_word_1353 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1353) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_28_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1353. apply global_local_1353.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1353_sync.
 - exact ran.
Qed.
Lemma global_field_1354_sync : field_sync_check generated_modules multiplier_instances [::] 29 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1354_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 29 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 29 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1354).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_29_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1354_sync.
 - exact ran.
Qed.
Lemma global_field_1354_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 0 snapshot = Some (Gval Fclock (global_word_0 v)))
 (initial_field : circuit_interface [::] 29 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1354 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1354 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 29 0 final = Some (Gval Fclock (global_word_1354 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1354) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_29_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1354. apply global_local_1354.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1354_sync.
 - exact ran.
Qed.
Lemma global_field_1355_sync : field_sync_check generated_modules multiplier_instances [::] 29 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1355_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 29 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 29 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1355).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_29_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1355_sync.
 - exact ran.
Qed.
Lemma global_field_1355_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 1 snapshot = Some (Gval (Fuint 1) (global_word_1 v)))
 (initial_field : circuit_interface [::] 29 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1355 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1355 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 29 1 final = Some (Gval (Fuint 1) (global_word_1355 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1355) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_29_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1355. apply global_local_1355.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1355_sync.
 - exact ran.
Qed.
Lemma global_field_1356_sync : field_sync_check generated_modules multiplier_instances [::] 30 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1356_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 30 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 30 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1356).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_30_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1356_sync.
 - exact ran.
Qed.
Lemma global_field_1356_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 0 snapshot = Some (Gval Fclock (global_word_0 v)))
 (initial_field : circuit_interface [::] 30 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1356 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1356 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 30 0 final = Some (Gval Fclock (global_word_1356 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1356) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_30_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1356. apply global_local_1356.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1356_sync.
 - exact ran.
Qed.
Lemma global_field_1357_sync : field_sync_check generated_modules multiplier_instances [::] 30 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1357_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 30 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 30 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1357).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_30_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1357_sync.
 - exact ran.
Qed.
Lemma global_field_1357_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 1 snapshot = Some (Gval (Fuint 1) (global_word_1 v)))
 (initial_field : circuit_interface [::] 30 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1357 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1357 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 30 1 final = Some (Gval (Fuint 1) (global_word_1357 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1357) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_30_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1357. apply global_local_1357.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1357_sync.
 - exact ran.
Qed.
Lemma global_field_1358_sync : field_sync_check generated_modules multiplier_instances [::] 31 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1358_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 31 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 31 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1358).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_31_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1358_sync.
 - exact ran.
Qed.
Lemma global_field_1358_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 0 snapshot = Some (Gval Fclock (global_word_0 v)))
 (initial_field : circuit_interface [::] 31 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1358 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1358 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 31 0 final = Some (Gval Fclock (global_word_1358 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1358) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_31_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1358. apply global_local_1358.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1358_sync.
 - exact ran.
Qed.
Lemma global_field_1359_sync : field_sync_check generated_modules multiplier_instances [::] 31 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1359_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 31 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 31 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1359).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_31_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1359_sync.
 - exact ran.
Qed.
Lemma global_field_1359_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 1 snapshot = Some (Gval (Fuint 1) (global_word_1 v)))
 (initial_field : circuit_interface [::] 31 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1359 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1359 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 31 1 final = Some (Gval (Fuint 1) (global_word_1359 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1359) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_31_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1359. apply global_local_1359.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1359_sync.
 - exact ran.
Qed.
Lemma global_field_1360_sync : field_sync_check generated_modules multiplier_instances [::] 32 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1360_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 32 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 32 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1360).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_32_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1360_sync.
 - exact ran.
Qed.
Lemma global_field_1360_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 0 snapshot = Some (Gval Fclock (global_word_0 v)))
 (initial_field : circuit_interface [::] 32 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1360 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1360 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 32 0 final = Some (Gval Fclock (global_word_1360 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1360) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_32_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1360. apply global_local_1360.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1360_sync.
 - exact ran.
Qed.
Lemma global_field_1361_sync : field_sync_check generated_modules multiplier_instances [::] 32 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1361_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 32 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 32 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1361).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_32_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1361_sync.
 - exact ran.
Qed.
Lemma global_field_1361_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 1 snapshot = Some (Gval (Fuint 1) (global_word_1 v)))
 (initial_field : circuit_interface [::] 32 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1361 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1361 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 32 1 final = Some (Gval (Fuint 1) (global_word_1361 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1361) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_32_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1361. apply global_local_1361.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1361_sync.
 - exact ran.
Qed.
Lemma global_field_1362_sync : field_sync_check generated_modules multiplier_instances [::] 33 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1362_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 33 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 33 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1362).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_33_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1362_sync.
 - exact ran.
Qed.
Lemma global_field_1362_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 0 snapshot = Some (Gval Fclock (global_word_0 v)))
 (initial_field : circuit_interface [::] 33 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1362 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1362 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 33 0 final = Some (Gval Fclock (global_word_1362 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1362) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_33_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1362. apply global_local_1362.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1362_sync.
 - exact ran.
Qed.
Lemma global_field_1363_sync : field_sync_check generated_modules multiplier_instances [::] 33 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1363_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 33 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 33 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1363).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_33_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1363_sync.
 - exact ran.
Qed.
Lemma global_field_1363_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 1 snapshot = Some (Gval (Fuint 1) (global_word_1 v)))
 (initial_field : circuit_interface [::] 33 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1363 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1363 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 33 1 final = Some (Gval (Fuint 1) (global_word_1363 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1363) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_33_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1363. apply global_local_1363.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1363_sync.
 - exact ran.
Qed.
Lemma global_field_1364_sync : field_sync_check generated_modules multiplier_instances [::] 34 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1364_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 34 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 34 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1364).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_34_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1364_sync.
 - exact ran.
Qed.
Lemma global_field_1364_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 0 snapshot = Some (Gval Fclock (global_word_0 v)))
 (initial_field : circuit_interface [::] 34 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1364 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1364 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 34 0 final = Some (Gval Fclock (global_word_1364 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1364) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_34_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1364. apply global_local_1364.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1364_sync.
 - exact ran.
Qed.
Lemma global_field_1365_sync : field_sync_check generated_modules multiplier_instances [::] 34 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1365_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 34 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 34 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1365).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_34_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1365_sync.
 - exact ran.
Qed.
Lemma global_field_1365_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 1 snapshot = Some (Gval (Fuint 1) (global_word_1 v)))
 (initial_field : circuit_interface [::] 34 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1365 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1365 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 34 1 final = Some (Gval (Fuint 1) (global_word_1365 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1365) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_34_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1365. apply global_local_1365.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1365_sync.
 - exact ran.
Qed.
Lemma global_field_1366_sync : field_sync_check generated_modules multiplier_instances [::] 35 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1366_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 35 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 35 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1366).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_35_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1366_sync.
 - exact ran.
Qed.
Lemma global_field_1366_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 0 snapshot = Some (Gval Fclock (global_word_0 v)))
 (initial_field : circuit_interface [::] 35 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1366 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1366 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 35 0 final = Some (Gval Fclock (global_word_1366 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1366) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_35_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1366. apply global_local_1366.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1366_sync.
 - exact ran.
Qed.
Lemma global_field_1367_sync : field_sync_check generated_modules multiplier_instances [::] 35 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1367_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 35 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 35 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1367).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_35_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1367_sync.
 - exact ran.
Qed.
Lemma global_field_1367_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 1 snapshot = Some (Gval (Fuint 1) (global_word_1 v)))
 (initial_field : circuit_interface [::] 35 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1367 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1367 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 35 1 final = Some (Gval (Fuint 1) (global_word_1367 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1367) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_35_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1367. apply global_local_1367.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1367_sync.
 - exact ran.
Qed.
Lemma global_field_1368_sync : field_sync_check generated_modules multiplier_instances [::] 36 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1368_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 36 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 36 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1368).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_36_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1368_sync.
 - exact ran.
Qed.
Lemma global_field_1368_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 0 snapshot = Some (Gval Fclock (global_word_0 v)))
 (initial_field : circuit_interface [::] 36 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1368 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1368 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 36 0 final = Some (Gval Fclock (global_word_1368 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1368) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_36_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1368. apply global_local_1368.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1368_sync.
 - exact ran.
Qed.
Lemma global_field_1369_sync : field_sync_check generated_modules multiplier_instances [::] 36 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1369_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::] 36 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::] 36 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1369).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_36_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1369_sync.
 - exact ran.
Qed.
Lemma global_field_1369_step invalid snapshot final v initial
 (H0 : circuit_lookup [::] 1 snapshot = Some (Gval (Fuint 1) (global_word_1 v)))
 (initial_field : circuit_interface [::] 36 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1369 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1369 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::] 36 1 final = Some (Gval (Fuint 1) (global_word_1369 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (rhs:=global_expr_1369) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_3_36_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1369. apply global_local_1369.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1369_sync.
 - exact ran.
Qed.
Lemma global_field_1464_sync : field_sync_check generated_modules multiplier_instances [::11] 10 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1464_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::11] 10 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::11] 10 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1464).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1464_sync.
 - exact ran.
Qed.
Lemma global_field_1464_step invalid snapshot final v initial
 (H0 : circuit_lookup [::11] 0 snapshot = Some (Gval Fclock (global_word_1463 v)))
 (initial_field : circuit_interface [::11] 10 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1464 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1464 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::11] 10 0 final = Some (Gval Fclock (global_word_1464 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1464) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1464. apply global_local_1464.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1464_sync.
 - exact ran.
Qed.
Lemma global_field_1465_sync : field_sync_check generated_modules multiplier_instances [::11] 10 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1465_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::11] 10 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::11] 10 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1465).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1465_sync.
 - exact ran.
Qed.
Lemma global_field_1465_step invalid snapshot final v initial
 (H0 : circuit_lookup [::11] 1 snapshot = Some (Gval (Fuint 1) (global_word_1459 v)))
 (initial_field : circuit_interface [::11] 10 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1465 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1465 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::11] 10 1 final = Some (Gval (Fuint 1) (global_word_1465 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1465) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1465. apply global_local_1465.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1465_sync.
 - exact ran.
Qed.
Lemma global_field_1466_sync : field_sync_check generated_modules multiplier_instances [::11] 11 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1466_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::11] 11 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::11] 11 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1466).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1466_sync.
 - exact ran.
Qed.
Lemma global_field_1466_step invalid snapshot final v initial
 (H0 : circuit_lookup [::11] 0 snapshot = Some (Gval Fclock (global_word_1463 v)))
 (initial_field : circuit_interface [::11] 11 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1466 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1466 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::11] 11 0 final = Some (Gval Fclock (global_word_1466 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1466) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1466. apply global_local_1466.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1466_sync.
 - exact ran.
Qed.
Lemma global_field_1467_sync : field_sync_check generated_modules multiplier_instances [::11] 11 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1467_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::11] 11 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::11] 11 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1467).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1467_sync.
 - exact ran.
Qed.
Lemma global_field_1467_step invalid snapshot final v initial
 (H0 : circuit_lookup [::11] 1 snapshot = Some (Gval (Fuint 1) (global_word_1459 v)))
 (initial_field : circuit_interface [::11] 11 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1467 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1467 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::11] 11 1 final = Some (Gval (Fuint 1) (global_word_1467 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1467) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1467. apply global_local_1467.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1467_sync.
 - exact ran.
Qed.
Lemma global_field_1532_sync : field_sync_check generated_modules multiplier_instances [::12] 10 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1532_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::12] 10 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::12] 10 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1532).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1532_sync.
 - exact ran.
Qed.
Lemma global_field_1532_step invalid snapshot final v initial
 (H0 : circuit_lookup [::12] 0 snapshot = Some (Gval Fclock (global_word_1531 v)))
 (initial_field : circuit_interface [::12] 10 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1532 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1532 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::12] 10 0 final = Some (Gval Fclock (global_word_1532 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1532) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1532. apply global_local_1532.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1532_sync.
 - exact ran.
Qed.
Lemma global_field_1533_sync : field_sync_check generated_modules multiplier_instances [::12] 10 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1533_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::12] 10 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::12] 10 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1533).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1533_sync.
 - exact ran.
Qed.
Lemma global_field_1533_step invalid snapshot final v initial
 (H0 : circuit_lookup [::12] 1 snapshot = Some (Gval (Fuint 1) (global_word_1527 v)))
 (initial_field : circuit_interface [::12] 10 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1533 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1533 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::12] 10 1 final = Some (Gval (Fuint 1) (global_word_1533 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1533) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1533. apply global_local_1533.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1533_sync.
 - exact ran.
Qed.
Lemma global_field_1534_sync : field_sync_check generated_modules multiplier_instances [::12] 11 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1534_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::12] 11 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::12] 11 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1534).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1534_sync.
 - exact ran.
Qed.
Lemma global_field_1534_step invalid snapshot final v initial
 (H0 : circuit_lookup [::12] 0 snapshot = Some (Gval Fclock (global_word_1531 v)))
 (initial_field : circuit_interface [::12] 11 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1534 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1534 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::12] 11 0 final = Some (Gval Fclock (global_word_1534 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1534) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1534. apply global_local_1534.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1534_sync.
 - exact ran.
Qed.
Lemma global_field_1535_sync : field_sync_check generated_modules multiplier_instances [::12] 11 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1535_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::12] 11 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::12] 11 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1535).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1535_sync.
 - exact ran.
Qed.
Lemma global_field_1535_step invalid snapshot final v initial
 (H0 : circuit_lookup [::12] 1 snapshot = Some (Gval (Fuint 1) (global_word_1527 v)))
 (initial_field : circuit_interface [::12] 11 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1535 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1535 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::12] 11 1 final = Some (Gval (Fuint 1) (global_word_1535 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1535) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1535. apply global_local_1535.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1535_sync.
 - exact ran.
Qed.
Lemma global_field_1600_sync : field_sync_check generated_modules multiplier_instances [::13] 10 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1600_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::13] 10 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::13] 10 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1600).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1600_sync.
 - exact ran.
Qed.
Lemma global_field_1600_step invalid snapshot final v initial
 (H0 : circuit_lookup [::13] 0 snapshot = Some (Gval Fclock (global_word_1599 v)))
 (initial_field : circuit_interface [::13] 10 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1600 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1600 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::13] 10 0 final = Some (Gval Fclock (global_word_1600 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1600) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1600. apply global_local_1600.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1600_sync.
 - exact ran.
Qed.
Lemma global_field_1601_sync : field_sync_check generated_modules multiplier_instances [::13] 10 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1601_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::13] 10 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::13] 10 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1601).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1601_sync.
 - exact ran.
Qed.
Lemma global_field_1601_step invalid snapshot final v initial
 (H0 : circuit_lookup [::13] 1 snapshot = Some (Gval (Fuint 1) (global_word_1595 v)))
 (initial_field : circuit_interface [::13] 10 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1601 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1601 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::13] 10 1 final = Some (Gval (Fuint 1) (global_word_1601 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1601) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1601. apply global_local_1601.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1601_sync.
 - exact ran.
Qed.
Lemma global_field_1602_sync : field_sync_check generated_modules multiplier_instances [::13] 11 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1602_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::13] 11 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::13] 11 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1602).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1602_sync.
 - exact ran.
Qed.
Lemma global_field_1602_step invalid snapshot final v initial
 (H0 : circuit_lookup [::13] 0 snapshot = Some (Gval Fclock (global_word_1599 v)))
 (initial_field : circuit_interface [::13] 11 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1602 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1602 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::13] 11 0 final = Some (Gval Fclock (global_word_1602 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1602) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1602. apply global_local_1602.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1602_sync.
 - exact ran.
Qed.
Lemma global_field_1603_sync : field_sync_check generated_modules multiplier_instances [::13] 11 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1603_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::13] 11 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::13] 11 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1603).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1603_sync.
 - exact ran.
Qed.
Lemma global_field_1603_step invalid snapshot final v initial
 (H0 : circuit_lookup [::13] 1 snapshot = Some (Gval (Fuint 1) (global_word_1595 v)))
 (initial_field : circuit_interface [::13] 11 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1603 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1603 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::13] 11 1 final = Some (Gval (Fuint 1) (global_word_1603 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1603) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1603. apply global_local_1603.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1603_sync.
 - exact ran.
Qed.
Lemma global_field_1668_sync : field_sync_check generated_modules multiplier_instances [::14] 10 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1668_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::14] 10 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::14] 10 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1668).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1668_sync.
 - exact ran.
Qed.
Lemma global_field_1668_step invalid snapshot final v initial
 (H0 : circuit_lookup [::14] 0 snapshot = Some (Gval Fclock (global_word_1667 v)))
 (initial_field : circuit_interface [::14] 10 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1668 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1668 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::14] 10 0 final = Some (Gval Fclock (global_word_1668 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1668) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1668. apply global_local_1668.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1668_sync.
 - exact ran.
Qed.
Lemma global_field_1669_sync : field_sync_check generated_modules multiplier_instances [::14] 10 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1669_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::14] 10 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::14] 10 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1669).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1669_sync.
 - exact ran.
Qed.
Lemma global_field_1669_step invalid snapshot final v initial
 (H0 : circuit_lookup [::14] 1 snapshot = Some (Gval (Fuint 1) (global_word_1663 v)))
 (initial_field : circuit_interface [::14] 10 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1669 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1669 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::14] 10 1 final = Some (Gval (Fuint 1) (global_word_1669 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1669) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1669. apply global_local_1669.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1669_sync.
 - exact ran.
Qed.
Lemma global_field_1670_sync : field_sync_check generated_modules multiplier_instances [::14] 11 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1670_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::14] 11 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::14] 11 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1670).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1670_sync.
 - exact ran.
Qed.
Lemma global_field_1670_step invalid snapshot final v initial
 (H0 : circuit_lookup [::14] 0 snapshot = Some (Gval Fclock (global_word_1667 v)))
 (initial_field : circuit_interface [::14] 11 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1670 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1670 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::14] 11 0 final = Some (Gval Fclock (global_word_1670 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1670) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1670. apply global_local_1670.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1670_sync.
 - exact ran.
Qed.
Lemma global_field_1671_sync : field_sync_check generated_modules multiplier_instances [::14] 11 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1671_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::14] 11 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::14] 11 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1671).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1671_sync.
 - exact ran.
Qed.
Lemma global_field_1671_step invalid snapshot final v initial
 (H0 : circuit_lookup [::14] 1 snapshot = Some (Gval (Fuint 1) (global_word_1663 v)))
 (initial_field : circuit_interface [::14] 11 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1671 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1671 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::14] 11 1 final = Some (Gval (Fuint 1) (global_word_1671 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1671) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1671. apply global_local_1671.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1671_sync.
 - exact ran.
Qed.
Lemma global_field_1736_sync : field_sync_check generated_modules multiplier_instances [::15] 10 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1736_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::15] 10 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::15] 10 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1736).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1736_sync.
 - exact ran.
Qed.
Lemma global_field_1736_step invalid snapshot final v initial
 (H0 : circuit_lookup [::15] 0 snapshot = Some (Gval Fclock (global_word_1735 v)))
 (initial_field : circuit_interface [::15] 10 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1736 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1736 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::15] 10 0 final = Some (Gval Fclock (global_word_1736 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1736) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1736. apply global_local_1736.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1736_sync.
 - exact ran.
Qed.
Lemma global_field_1737_sync : field_sync_check generated_modules multiplier_instances [::15] 10 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1737_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::15] 10 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::15] 10 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1737).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1737_sync.
 - exact ran.
Qed.
Lemma global_field_1737_step invalid snapshot final v initial
 (H0 : circuit_lookup [::15] 1 snapshot = Some (Gval (Fuint 1) (global_word_1731 v)))
 (initial_field : circuit_interface [::15] 10 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1737 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1737 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::15] 10 1 final = Some (Gval (Fuint 1) (global_word_1737 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1737) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1737. apply global_local_1737.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1737_sync.
 - exact ran.
Qed.
Lemma global_field_1738_sync : field_sync_check generated_modules multiplier_instances [::15] 11 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1738_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::15] 11 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::15] 11 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1738).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1738_sync.
 - exact ran.
Qed.
Lemma global_field_1738_step invalid snapshot final v initial
 (H0 : circuit_lookup [::15] 0 snapshot = Some (Gval Fclock (global_word_1735 v)))
 (initial_field : circuit_interface [::15] 11 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1738 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1738 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::15] 11 0 final = Some (Gval Fclock (global_word_1738 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1738) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1738. apply global_local_1738.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1738_sync.
 - exact ran.
Qed.
Lemma global_field_1739_sync : field_sync_check generated_modules multiplier_instances [::15] 11 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1739_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::15] 11 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::15] 11 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1739).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1739_sync.
 - exact ran.
Qed.
Lemma global_field_1739_step invalid snapshot final v initial
 (H0 : circuit_lookup [::15] 1 snapshot = Some (Gval (Fuint 1) (global_word_1731 v)))
 (initial_field : circuit_interface [::15] 11 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1739 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1739 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::15] 11 1 final = Some (Gval (Fuint 1) (global_word_1739 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1739) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1739. apply global_local_1739.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1739_sync.
 - exact ran.
Qed.
Lemma global_field_1804_sync : field_sync_check generated_modules multiplier_instances [::16] 10 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1804_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::16] 10 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::16] 10 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1804).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1804_sync.
 - exact ran.
Qed.
Lemma global_field_1804_step invalid snapshot final v initial
 (H0 : circuit_lookup [::16] 0 snapshot = Some (Gval Fclock (global_word_1803 v)))
 (initial_field : circuit_interface [::16] 10 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1804 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1804 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::16] 10 0 final = Some (Gval Fclock (global_word_1804 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1804) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1804. apply global_local_1804.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1804_sync.
 - exact ran.
Qed.
Lemma global_field_1805_sync : field_sync_check generated_modules multiplier_instances [::16] 10 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1805_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::16] 10 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::16] 10 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1805).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1805_sync.
 - exact ran.
Qed.
Lemma global_field_1805_step invalid snapshot final v initial
 (H0 : circuit_lookup [::16] 1 snapshot = Some (Gval (Fuint 1) (global_word_1799 v)))
 (initial_field : circuit_interface [::16] 10 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1805 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1805 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::16] 10 1 final = Some (Gval (Fuint 1) (global_word_1805 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1805) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1805. apply global_local_1805.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1805_sync.
 - exact ran.
Qed.
Lemma global_field_1806_sync : field_sync_check generated_modules multiplier_instances [::16] 11 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1806_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::16] 11 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::16] 11 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1806).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1806_sync.
 - exact ran.
Qed.
Lemma global_field_1806_step invalid snapshot final v initial
 (H0 : circuit_lookup [::16] 0 snapshot = Some (Gval Fclock (global_word_1803 v)))
 (initial_field : circuit_interface [::16] 11 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1806 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1806 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::16] 11 0 final = Some (Gval Fclock (global_word_1806 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1806) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1806. apply global_local_1806.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1806_sync.
 - exact ran.
Qed.
Lemma global_field_1807_sync : field_sync_check generated_modules multiplier_instances [::16] 11 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1807_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::16] 11 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::16] 11 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1807).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1807_sync.
 - exact ran.
Qed.
Lemma global_field_1807_step invalid snapshot final v initial
 (H0 : circuit_lookup [::16] 1 snapshot = Some (Gval (Fuint 1) (global_word_1799 v)))
 (initial_field : circuit_interface [::16] 11 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1807 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1807 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::16] 11 1 final = Some (Gval (Fuint 1) (global_word_1807 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1807) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1807. apply global_local_1807.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1807_sync.
 - exact ran.
Qed.
Lemma global_field_1872_sync : field_sync_check generated_modules multiplier_instances [::17] 10 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1872_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::17] 10 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::17] 10 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1872).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1872_sync.
 - exact ran.
Qed.
Lemma global_field_1872_step invalid snapshot final v initial
 (H0 : circuit_lookup [::17] 0 snapshot = Some (Gval Fclock (global_word_1871 v)))
 (initial_field : circuit_interface [::17] 10 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1872 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1872 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::17] 10 0 final = Some (Gval Fclock (global_word_1872 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1872) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1872. apply global_local_1872.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1872_sync.
 - exact ran.
Qed.
Lemma global_field_1873_sync : field_sync_check generated_modules multiplier_instances [::17] 10 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1873_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::17] 10 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::17] 10 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1873).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1873_sync.
 - exact ran.
Qed.
Lemma global_field_1873_step invalid snapshot final v initial
 (H0 : circuit_lookup [::17] 1 snapshot = Some (Gval (Fuint 1) (global_word_1867 v)))
 (initial_field : circuit_interface [::17] 10 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1873 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1873 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::17] 10 1 final = Some (Gval (Fuint 1) (global_word_1873 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1873) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1873. apply global_local_1873.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1873_sync.
 - exact ran.
Qed.
Lemma global_field_1874_sync : field_sync_check generated_modules multiplier_instances [::17] 11 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1874_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::17] 11 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::17] 11 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1874).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1874_sync.
 - exact ran.
Qed.
Lemma global_field_1874_step invalid snapshot final v initial
 (H0 : circuit_lookup [::17] 0 snapshot = Some (Gval Fclock (global_word_1871 v)))
 (initial_field : circuit_interface [::17] 11 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1874 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1874 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::17] 11 0 final = Some (Gval Fclock (global_word_1874 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1874) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1874. apply global_local_1874.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1874_sync.
 - exact ran.
Qed.
Lemma global_field_1875_sync : field_sync_check generated_modules multiplier_instances [::17] 11 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1875_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::17] 11 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::17] 11 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1875).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1875_sync.
 - exact ran.
Qed.
Lemma global_field_1875_step invalid snapshot final v initial
 (H0 : circuit_lookup [::17] 1 snapshot = Some (Gval (Fuint 1) (global_word_1867 v)))
 (initial_field : circuit_interface [::17] 11 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1875 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1875 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::17] 11 1 final = Some (Gval (Fuint 1) (global_word_1875 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1875) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1875. apply global_local_1875.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1875_sync.
 - exact ran.
Qed.
Lemma global_field_1940_sync : field_sync_check generated_modules multiplier_instances [::18] 10 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1940_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::18] 10 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::18] 10 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1940).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1940_sync.
 - exact ran.
Qed.
Lemma global_field_1940_step invalid snapshot final v initial
 (H0 : circuit_lookup [::18] 0 snapshot = Some (Gval Fclock (global_word_1939 v)))
 (initial_field : circuit_interface [::18] 10 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1940 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1940 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::18] 10 0 final = Some (Gval Fclock (global_word_1940 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1940) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1940. apply global_local_1940.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1940_sync.
 - exact ran.
Qed.
Lemma global_field_1941_sync : field_sync_check generated_modules multiplier_instances [::18] 10 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1941_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::18] 10 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::18] 10 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1941).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1941_sync.
 - exact ran.
Qed.
Lemma global_field_1941_step invalid snapshot final v initial
 (H0 : circuit_lookup [::18] 1 snapshot = Some (Gval (Fuint 1) (global_word_1935 v)))
 (initial_field : circuit_interface [::18] 10 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1941 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1941 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::18] 10 1 final = Some (Gval (Fuint 1) (global_word_1941 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1941) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_10_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1941. apply global_local_1941.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1941_sync.
 - exact ran.
Qed.
Lemma global_field_1942_sync : field_sync_check generated_modules multiplier_instances [::18] 11 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1942_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::18] 11 0 snapshot) = Some (Gtyp Fclock))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::18] 11 0 final) = Some (Gtyp Fclock).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1942).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1942_sync.
 - exact ran.
Qed.
Lemma global_field_1942_step invalid snapshot final v initial
 (H0 : circuit_lookup [::18] 0 snapshot = Some (Gval Fclock (global_word_1939 v)))
 (initial_field : circuit_interface [::18] 11 0 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp Fclock)
 (adapted : adapt_hvalue_as_type (Gval Fclock (global_word_1942 v)) (Gtyp Fclock) = Some (Gval Fclock (global_word_1942 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::18] 11 0 final = Some (Gval Fclock (global_word_1942 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1942) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_0_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1942. apply global_local_1942.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1942_sync.
 - exact ran.
Qed.
Lemma global_field_1943_sync : field_sync_check generated_modules multiplier_instances [::18] 11 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_field_1943_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface [::18] 11 1 snapshot) = Some (Gtyp (Fuint 1)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface [::18] 11 1 final) = Some (Gtyp (Fuint 1)).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1943).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_1943_sync.
 - exact ran.
Qed.
Lemma global_field_1943_step invalid snapshot final v initial
 (H0 : circuit_lookup [::18] 1 snapshot = Some (Gval (Fuint 1) (global_word_1935 v)))
 (initial_field : circuit_interface [::18] 11 1 snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp (Fuint 1))
 (adapted : adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1943 v)) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) (global_word_1943 v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface [::18] 11 1 final = Some (Gval (Fuint 1) (global_word_1943 v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (rhs:=global_expr_1943) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact field_2_11_1_certificate.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_1943. apply global_local_1943.
   + unfold circuit_lookup in H0. rewrite found in H0. exact H0.
 - exact adapted.
 - reflexivity.
 - exact global_field_1943_sync.
 - exact ran.
Qed.
