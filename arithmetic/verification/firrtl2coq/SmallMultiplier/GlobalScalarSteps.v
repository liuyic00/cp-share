From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import StatementFacts GroundFrames HierarchyFacts.
From SmallMultiplier Require Import Model GlobalStable GlobalInstances GlobalScalarFacts InstanceChecks ScalarCertificateCheck.
Local Open Scope N_scope.
Lemma global_scalar_289_syntax : framed_write_certificate 4
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 4) (@Eref VarOrder.T (@Eid VarOrder.T 25))) generated_module_0_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_289_sync : node_sync_check generated_modules multiplier_instances [::7] 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_289_type invalid snapshot final initial
 (initial_found:circuit_lookup [::7] 4 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::7] 4 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=25).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_289_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_289_sync.
 - exact ran.
Qed.
Lemma global_scalar_289_step invalid snapshot final v initial
 (source_found:circuit_lookup [::7] 25 snapshot=Some(Gval (Fuint 1) (global_word_288 v)))
 (initial_found:circuit_lookup [::7] 4 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_288 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_289 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::7] 4 final=Some(Gval (Fuint 1) (global_word_289 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=25).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_289_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_289_sync.
 - exact ran.
Qed.
Lemma global_scalar_293_syntax : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 26))) generated_module_0_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_293_sync : node_sync_check generated_modules multiplier_instances [::7] 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_293_type invalid snapshot final initial
 (initial_found:circuit_lookup [::7] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::7] 5 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=26).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_293_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_293_sync.
 - exact ran.
Qed.
Lemma global_scalar_293_step invalid snapshot final v initial
 (source_found:circuit_lookup [::7] 26 snapshot=Some(Gval (Fuint 1) (global_word_292 v)))
 (initial_found:circuit_lookup [::7] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_292 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_293 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::7] 5 final=Some(Gval (Fuint 1) (global_word_293 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=26).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_293_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_293_sync.
 - exact ran.
Qed.
Lemma global_scalar_307_syntax : framed_write_certificate 4
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 4) (@Eref VarOrder.T (@Eid VarOrder.T 25))) generated_module_0_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_307_sync : node_sync_check generated_modules multiplier_instances [::8] 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_307_type invalid snapshot final initial
 (initial_found:circuit_lookup [::8] 4 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::8] 4 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=25).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_307_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_307_sync.
 - exact ran.
Qed.
Lemma global_scalar_307_step invalid snapshot final v initial
 (source_found:circuit_lookup [::8] 25 snapshot=Some(Gval (Fuint 1) (global_word_306 v)))
 (initial_found:circuit_lookup [::8] 4 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_306 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_307 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::8] 4 final=Some(Gval (Fuint 1) (global_word_307 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=25).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_307_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_307_sync.
 - exact ran.
Qed.
Lemma global_scalar_311_syntax : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 26))) generated_module_0_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_311_sync : node_sync_check generated_modules multiplier_instances [::8] 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_311_type invalid snapshot final initial
 (initial_found:circuit_lookup [::8] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::8] 5 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=26).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_311_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_311_sync.
 - exact ran.
Qed.
Lemma global_scalar_311_step invalid snapshot final v initial
 (source_found:circuit_lookup [::8] 26 snapshot=Some(Gval (Fuint 1) (global_word_310 v)))
 (initial_found:circuit_lookup [::8] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_310 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_311 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::8] 5 final=Some(Gval (Fuint 1) (global_word_311 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=26).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_311_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_311_sync.
 - exact ran.
Qed.
Lemma global_scalar_331_syntax : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 33))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_331_sync : node_sync_check generated_modules multiplier_instances [::9] 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_331_type invalid snapshot final initial
 (initial_found:circuit_lookup [::9] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::9] 5 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_331_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_331_sync.
 - exact ran.
Qed.
Lemma global_scalar_331_step invalid snapshot final v initial
 (source_found:circuit_lookup [::9] 33 snapshot=Some(Gval (Fuint 1) (global_word_330 v)))
 (initial_found:circuit_lookup [::9] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_330 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_331 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::9] 5 final=Some(Gval (Fuint 1) (global_word_331 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_331_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_331_sync.
 - exact ran.
Qed.
Lemma global_scalar_335_syntax : framed_write_certificate 6
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 6) (@Eref VarOrder.T (@Eid VarOrder.T 34))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_335_sync : node_sync_check generated_modules multiplier_instances [::9] 6 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_335_type invalid snapshot final initial
 (initial_found:circuit_lookup [::9] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::9] 6 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_335_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_335_sync.
 - exact ran.
Qed.
Lemma global_scalar_335_step invalid snapshot final v initial
 (source_found:circuit_lookup [::9] 34 snapshot=Some(Gval (Fuint 1) (global_word_334 v)))
 (initial_found:circuit_lookup [::9] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_334 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_335 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::9] 6 final=Some(Gval (Fuint 1) (global_word_335 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_335_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_335_sync.
 - exact ran.
Qed.
Lemma global_scalar_355_syntax : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 33))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_355_sync : node_sync_check generated_modules multiplier_instances [::10] 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_355_type invalid snapshot final initial
 (initial_found:circuit_lookup [::10] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::10] 5 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_355_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_355_sync.
 - exact ran.
Qed.
Lemma global_scalar_355_step invalid snapshot final v initial
 (source_found:circuit_lookup [::10] 33 snapshot=Some(Gval (Fuint 1) (global_word_354 v)))
 (initial_found:circuit_lookup [::10] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_354 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_355 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10] 5 final=Some(Gval (Fuint 1) (global_word_355 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_355_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_355_sync.
 - exact ran.
Qed.
Lemma global_scalar_359_syntax : framed_write_certificate 6
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 6) (@Eref VarOrder.T (@Eid VarOrder.T 34))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_359_sync : node_sync_check generated_modules multiplier_instances [::10] 6 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_359_type invalid snapshot final initial
 (initial_found:circuit_lookup [::10] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::10] 6 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_359_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_359_sync.
 - exact ran.
Qed.
Lemma global_scalar_359_step invalid snapshot final v initial
 (source_found:circuit_lookup [::10] 34 snapshot=Some(Gval (Fuint 1) (global_word_358 v)))
 (initial_found:circuit_lookup [::10] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_358 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_359 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10] 6 final=Some(Gval (Fuint 1) (global_word_359 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_359_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_359_sync.
 - exact ran.
Qed.
Lemma global_scalar_391_syntax : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 33))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_391_sync : node_sync_check generated_modules multiplier_instances [::10;11] 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_391_type invalid snapshot final initial
 (initial_found:circuit_lookup [::10;11] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::10;11] 5 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_391_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_391_sync.
 - exact ran.
Qed.
Lemma global_scalar_391_step invalid snapshot final v initial
 (source_found:circuit_lookup [::10;11] 33 snapshot=Some(Gval (Fuint 1) (global_word_390 v)))
 (initial_found:circuit_lookup [::10;11] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_390 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_391 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;11] 5 final=Some(Gval (Fuint 1) (global_word_391 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_391_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_391_sync.
 - exact ran.
Qed.
Lemma global_scalar_411_syntax : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 33))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_411_sync : node_sync_check generated_modules multiplier_instances [::11;11] 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_411_type invalid snapshot final initial
 (initial_found:circuit_lookup [::11;11] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::11;11] 5 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_411_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_411_sync.
 - exact ran.
Qed.
Lemma global_scalar_411_step invalid snapshot final v initial
 (source_found:circuit_lookup [::11;11] 33 snapshot=Some(Gval (Fuint 1) (global_word_410 v)))
 (initial_found:circuit_lookup [::11;11] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_410 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_411 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;11] 5 final=Some(Gval (Fuint 1) (global_word_411 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_411_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_411_sync.
 - exact ran.
Qed.
Lemma global_scalar_414_syntax : framed_write_certificate 7
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 7) (@Eref VarOrder.T (@Eid VarOrder.T 41))) generated_module_2_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_414_sync : node_sync_check generated_modules multiplier_instances [::11] 7 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_414_type invalid snapshot final initial
 (initial_found:circuit_lookup [::11] 7 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::11] 7 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=41).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_414_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_414_sync.
 - exact ran.
Qed.
Lemma global_scalar_414_step invalid snapshot final v initial
 (source_found:circuit_lookup [::11] 41 snapshot=Some(Gval (Fuint 1) (global_word_413 v)))
 (initial_found:circuit_lookup [::11] 7 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_413 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_414 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11] 7 final=Some(Gval (Fuint 1) (global_word_414 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=41).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_414_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_414_sync.
 - exact ran.
Qed.
Lemma global_scalar_418_syntax : framed_write_certificate 6
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 6) (@Eref VarOrder.T (@Eid VarOrder.T 34))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_418_sync : node_sync_check generated_modules multiplier_instances [::10;11] 6 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_418_type invalid snapshot final initial
 (initial_found:circuit_lookup [::10;11] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::10;11] 6 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_418_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_418_sync.
 - exact ran.
Qed.
Lemma global_scalar_418_step invalid snapshot final v initial
 (source_found:circuit_lookup [::10;11] 34 snapshot=Some(Gval (Fuint 1) (global_word_417 v)))
 (initial_found:circuit_lookup [::10;11] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_417 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_418 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;11] 6 final=Some(Gval (Fuint 1) (global_word_418 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_418_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_418_sync.
 - exact ran.
Qed.
Lemma global_scalar_421_syntax : framed_write_certificate 8
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 8) (@Eref VarOrder.T (@Eid VarOrder.T 42))) generated_module_2_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_421_sync : node_sync_check generated_modules multiplier_instances [::11] 8 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_421_type invalid snapshot final initial
 (initial_found:circuit_lookup [::11] 8 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::11] 8 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=42).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_421_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_421_sync.
 - exact ran.
Qed.
Lemma global_scalar_421_step invalid snapshot final v initial
 (source_found:circuit_lookup [::11] 42 snapshot=Some(Gval (Fuint 1) (global_word_420 v)))
 (initial_found:circuit_lookup [::11] 8 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_420 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_421 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11] 8 final=Some(Gval (Fuint 1) (global_word_421 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=42).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_421_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_421_sync.
 - exact ran.
Qed.
Lemma global_scalar_425_syntax : framed_write_certificate 6
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 6) (@Eref VarOrder.T (@Eid VarOrder.T 34))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_425_sync : node_sync_check generated_modules multiplier_instances [::11;11] 6 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_425_type invalid snapshot final initial
 (initial_found:circuit_lookup [::11;11] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::11;11] 6 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_425_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_425_sync.
 - exact ran.
Qed.
Lemma global_scalar_425_step invalid snapshot final v initial
 (source_found:circuit_lookup [::11;11] 34 snapshot=Some(Gval (Fuint 1) (global_word_424 v)))
 (initial_found:circuit_lookup [::11;11] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_424 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_425 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;11] 6 final=Some(Gval (Fuint 1) (global_word_425 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_425_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_425_sync.
 - exact ran.
Qed.
Lemma global_scalar_428_syntax : framed_write_certificate 9
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 9) (@Eref VarOrder.T (@Eid VarOrder.T 43))) generated_module_2_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_428_sync : node_sync_check generated_modules multiplier_instances [::11] 9 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_428_type invalid snapshot final initial
 (initial_found:circuit_lookup [::11] 9 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::11] 9 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=43).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_428_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_428_sync.
 - exact ran.
Qed.
Lemma global_scalar_428_step invalid snapshot final v initial
 (source_found:circuit_lookup [::11] 43 snapshot=Some(Gval (Fuint 1) (global_word_427 v)))
 (initial_found:circuit_lookup [::11] 9 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_427 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_428 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11] 9 final=Some(Gval (Fuint 1) (global_word_428 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=43).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_428_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_428_sync.
 - exact ran.
Qed.
Lemma global_scalar_460_syntax : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 33))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_460_sync : node_sync_check generated_modules multiplier_instances [::10;12] 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_460_type invalid snapshot final initial
 (initial_found:circuit_lookup [::10;12] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::10;12] 5 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_460_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_460_sync.
 - exact ran.
Qed.
Lemma global_scalar_460_step invalid snapshot final v initial
 (source_found:circuit_lookup [::10;12] 33 snapshot=Some(Gval (Fuint 1) (global_word_459 v)))
 (initial_found:circuit_lookup [::10;12] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_459 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_460 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;12] 5 final=Some(Gval (Fuint 1) (global_word_460 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_460_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_460_sync.
 - exact ran.
Qed.
Lemma global_scalar_480_syntax : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 33))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_480_sync : node_sync_check generated_modules multiplier_instances [::11;12] 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_480_type invalid snapshot final initial
 (initial_found:circuit_lookup [::11;12] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::11;12] 5 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_480_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_480_sync.
 - exact ran.
Qed.
Lemma global_scalar_480_step invalid snapshot final v initial
 (source_found:circuit_lookup [::11;12] 33 snapshot=Some(Gval (Fuint 1) (global_word_479 v)))
 (initial_found:circuit_lookup [::11;12] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_479 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_480 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;12] 5 final=Some(Gval (Fuint 1) (global_word_480 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_480_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_480_sync.
 - exact ran.
Qed.
Lemma global_scalar_483_syntax : framed_write_certificate 7
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 7) (@Eref VarOrder.T (@Eid VarOrder.T 41))) generated_module_2_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_483_sync : node_sync_check generated_modules multiplier_instances [::12] 7 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_483_type invalid snapshot final initial
 (initial_found:circuit_lookup [::12] 7 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::12] 7 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=41).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_483_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_483_sync.
 - exact ran.
Qed.
Lemma global_scalar_483_step invalid snapshot final v initial
 (source_found:circuit_lookup [::12] 41 snapshot=Some(Gval (Fuint 1) (global_word_482 v)))
 (initial_found:circuit_lookup [::12] 7 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_482 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_483 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::12] 7 final=Some(Gval (Fuint 1) (global_word_483 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=41).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_483_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_483_sync.
 - exact ran.
Qed.
Lemma global_scalar_487_syntax : framed_write_certificate 6
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 6) (@Eref VarOrder.T (@Eid VarOrder.T 34))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_487_sync : node_sync_check generated_modules multiplier_instances [::10;12] 6 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_487_type invalid snapshot final initial
 (initial_found:circuit_lookup [::10;12] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::10;12] 6 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_487_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_487_sync.
 - exact ran.
Qed.
Lemma global_scalar_487_step invalid snapshot final v initial
 (source_found:circuit_lookup [::10;12] 34 snapshot=Some(Gval (Fuint 1) (global_word_486 v)))
 (initial_found:circuit_lookup [::10;12] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_486 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_487 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;12] 6 final=Some(Gval (Fuint 1) (global_word_487 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_487_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_487_sync.
 - exact ran.
Qed.
Lemma global_scalar_490_syntax : framed_write_certificate 8
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 8) (@Eref VarOrder.T (@Eid VarOrder.T 42))) generated_module_2_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_490_sync : node_sync_check generated_modules multiplier_instances [::12] 8 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_490_type invalid snapshot final initial
 (initial_found:circuit_lookup [::12] 8 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::12] 8 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=42).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_490_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_490_sync.
 - exact ran.
Qed.
Lemma global_scalar_490_step invalid snapshot final v initial
 (source_found:circuit_lookup [::12] 42 snapshot=Some(Gval (Fuint 1) (global_word_489 v)))
 (initial_found:circuit_lookup [::12] 8 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_489 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_490 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::12] 8 final=Some(Gval (Fuint 1) (global_word_490 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=42).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_490_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_490_sync.
 - exact ran.
Qed.
Lemma global_scalar_494_syntax : framed_write_certificate 6
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 6) (@Eref VarOrder.T (@Eid VarOrder.T 34))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_494_sync : node_sync_check generated_modules multiplier_instances [::11;12] 6 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_494_type invalid snapshot final initial
 (initial_found:circuit_lookup [::11;12] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::11;12] 6 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_494_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_494_sync.
 - exact ran.
Qed.
Lemma global_scalar_494_step invalid snapshot final v initial
 (source_found:circuit_lookup [::11;12] 34 snapshot=Some(Gval (Fuint 1) (global_word_493 v)))
 (initial_found:circuit_lookup [::11;12] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_493 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_494 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;12] 6 final=Some(Gval (Fuint 1) (global_word_494 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_494_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_494_sync.
 - exact ran.
Qed.
Lemma global_scalar_497_syntax : framed_write_certificate 9
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 9) (@Eref VarOrder.T (@Eid VarOrder.T 43))) generated_module_2_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_497_sync : node_sync_check generated_modules multiplier_instances [::12] 9 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_497_type invalid snapshot final initial
 (initial_found:circuit_lookup [::12] 9 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::12] 9 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=43).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_497_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_497_sync.
 - exact ran.
Qed.
Lemma global_scalar_497_step invalid snapshot final v initial
 (source_found:circuit_lookup [::12] 43 snapshot=Some(Gval (Fuint 1) (global_word_496 v)))
 (initial_found:circuit_lookup [::12] 9 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_496 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_497 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::12] 9 final=Some(Gval (Fuint 1) (global_word_497 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=43).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_497_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_497_sync.
 - exact ran.
Qed.
Lemma global_scalar_529_syntax : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 33))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_529_sync : node_sync_check generated_modules multiplier_instances [::10;13] 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_529_type invalid snapshot final initial
 (initial_found:circuit_lookup [::10;13] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::10;13] 5 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_529_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_529_sync.
 - exact ran.
Qed.
Lemma global_scalar_529_step invalid snapshot final v initial
 (source_found:circuit_lookup [::10;13] 33 snapshot=Some(Gval (Fuint 1) (global_word_528 v)))
 (initial_found:circuit_lookup [::10;13] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_528 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_529 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;13] 5 final=Some(Gval (Fuint 1) (global_word_529 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_529_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_529_sync.
 - exact ran.
Qed.
Lemma global_scalar_549_syntax : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 33))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_549_sync : node_sync_check generated_modules multiplier_instances [::11;13] 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_549_type invalid snapshot final initial
 (initial_found:circuit_lookup [::11;13] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::11;13] 5 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_549_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_549_sync.
 - exact ran.
Qed.
Lemma global_scalar_549_step invalid snapshot final v initial
 (source_found:circuit_lookup [::11;13] 33 snapshot=Some(Gval (Fuint 1) (global_word_548 v)))
 (initial_found:circuit_lookup [::11;13] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_548 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_549 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;13] 5 final=Some(Gval (Fuint 1) (global_word_549 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_549_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_549_sync.
 - exact ran.
Qed.
Lemma global_scalar_552_syntax : framed_write_certificate 7
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 7) (@Eref VarOrder.T (@Eid VarOrder.T 41))) generated_module_2_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_552_sync : node_sync_check generated_modules multiplier_instances [::13] 7 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_552_type invalid snapshot final initial
 (initial_found:circuit_lookup [::13] 7 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::13] 7 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=41).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_552_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_552_sync.
 - exact ran.
Qed.
Lemma global_scalar_552_step invalid snapshot final v initial
 (source_found:circuit_lookup [::13] 41 snapshot=Some(Gval (Fuint 1) (global_word_551 v)))
 (initial_found:circuit_lookup [::13] 7 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_551 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_552 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::13] 7 final=Some(Gval (Fuint 1) (global_word_552 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=41).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_552_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_552_sync.
 - exact ran.
Qed.
Lemma global_scalar_556_syntax : framed_write_certificate 6
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 6) (@Eref VarOrder.T (@Eid VarOrder.T 34))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_556_sync : node_sync_check generated_modules multiplier_instances [::10;13] 6 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_556_type invalid snapshot final initial
 (initial_found:circuit_lookup [::10;13] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::10;13] 6 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_556_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_556_sync.
 - exact ran.
Qed.
Lemma global_scalar_556_step invalid snapshot final v initial
 (source_found:circuit_lookup [::10;13] 34 snapshot=Some(Gval (Fuint 1) (global_word_555 v)))
 (initial_found:circuit_lookup [::10;13] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_555 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_556 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;13] 6 final=Some(Gval (Fuint 1) (global_word_556 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_556_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_556_sync.
 - exact ran.
Qed.
Lemma global_scalar_559_syntax : framed_write_certificate 8
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 8) (@Eref VarOrder.T (@Eid VarOrder.T 42))) generated_module_2_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_559_sync : node_sync_check generated_modules multiplier_instances [::13] 8 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_559_type invalid snapshot final initial
 (initial_found:circuit_lookup [::13] 8 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::13] 8 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=42).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_559_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_559_sync.
 - exact ran.
Qed.
Lemma global_scalar_559_step invalid snapshot final v initial
 (source_found:circuit_lookup [::13] 42 snapshot=Some(Gval (Fuint 1) (global_word_558 v)))
 (initial_found:circuit_lookup [::13] 8 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_558 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_559 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::13] 8 final=Some(Gval (Fuint 1) (global_word_559 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=42).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_559_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_559_sync.
 - exact ran.
Qed.
Lemma global_scalar_563_syntax : framed_write_certificate 6
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 6) (@Eref VarOrder.T (@Eid VarOrder.T 34))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_563_sync : node_sync_check generated_modules multiplier_instances [::11;13] 6 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_563_type invalid snapshot final initial
 (initial_found:circuit_lookup [::11;13] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::11;13] 6 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_563_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_563_sync.
 - exact ran.
Qed.
Lemma global_scalar_563_step invalid snapshot final v initial
 (source_found:circuit_lookup [::11;13] 34 snapshot=Some(Gval (Fuint 1) (global_word_562 v)))
 (initial_found:circuit_lookup [::11;13] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_562 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_563 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;13] 6 final=Some(Gval (Fuint 1) (global_word_563 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_563_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_563_sync.
 - exact ran.
Qed.
Lemma global_scalar_566_syntax : framed_write_certificate 9
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 9) (@Eref VarOrder.T (@Eid VarOrder.T 43))) generated_module_2_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_566_sync : node_sync_check generated_modules multiplier_instances [::13] 9 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_566_type invalid snapshot final initial
 (initial_found:circuit_lookup [::13] 9 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::13] 9 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=43).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_566_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_566_sync.
 - exact ran.
Qed.
Lemma global_scalar_566_step invalid snapshot final v initial
 (source_found:circuit_lookup [::13] 43 snapshot=Some(Gval (Fuint 1) (global_word_565 v)))
 (initial_found:circuit_lookup [::13] 9 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_565 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_566 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::13] 9 final=Some(Gval (Fuint 1) (global_word_566 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=43).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_566_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_566_sync.
 - exact ran.
Qed.
Lemma global_scalar_598_syntax : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 33))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_598_sync : node_sync_check generated_modules multiplier_instances [::10;14] 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_598_type invalid snapshot final initial
 (initial_found:circuit_lookup [::10;14] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::10;14] 5 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_598_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_598_sync.
 - exact ran.
Qed.
Lemma global_scalar_598_step invalid snapshot final v initial
 (source_found:circuit_lookup [::10;14] 33 snapshot=Some(Gval (Fuint 1) (global_word_597 v)))
 (initial_found:circuit_lookup [::10;14] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_597 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_598 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;14] 5 final=Some(Gval (Fuint 1) (global_word_598 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_598_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_598_sync.
 - exact ran.
Qed.
Lemma global_scalar_618_syntax : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 33))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_618_sync : node_sync_check generated_modules multiplier_instances [::11;14] 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_618_type invalid snapshot final initial
 (initial_found:circuit_lookup [::11;14] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::11;14] 5 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_618_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_618_sync.
 - exact ran.
Qed.
Lemma global_scalar_618_step invalid snapshot final v initial
 (source_found:circuit_lookup [::11;14] 33 snapshot=Some(Gval (Fuint 1) (global_word_617 v)))
 (initial_found:circuit_lookup [::11;14] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_617 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_618 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;14] 5 final=Some(Gval (Fuint 1) (global_word_618 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_618_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_618_sync.
 - exact ran.
Qed.
Lemma global_scalar_621_syntax : framed_write_certificate 7
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 7) (@Eref VarOrder.T (@Eid VarOrder.T 41))) generated_module_2_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_621_sync : node_sync_check generated_modules multiplier_instances [::14] 7 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_621_type invalid snapshot final initial
 (initial_found:circuit_lookup [::14] 7 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::14] 7 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=41).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_621_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_621_sync.
 - exact ran.
Qed.
Lemma global_scalar_621_step invalid snapshot final v initial
 (source_found:circuit_lookup [::14] 41 snapshot=Some(Gval (Fuint 1) (global_word_620 v)))
 (initial_found:circuit_lookup [::14] 7 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_620 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_621 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::14] 7 final=Some(Gval (Fuint 1) (global_word_621 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=41).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_621_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_621_sync.
 - exact ran.
Qed.
Lemma global_scalar_625_syntax : framed_write_certificate 6
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 6) (@Eref VarOrder.T (@Eid VarOrder.T 34))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_625_sync : node_sync_check generated_modules multiplier_instances [::10;14] 6 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_625_type invalid snapshot final initial
 (initial_found:circuit_lookup [::10;14] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::10;14] 6 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_625_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_625_sync.
 - exact ran.
Qed.
Lemma global_scalar_625_step invalid snapshot final v initial
 (source_found:circuit_lookup [::10;14] 34 snapshot=Some(Gval (Fuint 1) (global_word_624 v)))
 (initial_found:circuit_lookup [::10;14] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_624 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_625 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;14] 6 final=Some(Gval (Fuint 1) (global_word_625 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_625_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_625_sync.
 - exact ran.
Qed.
Lemma global_scalar_628_syntax : framed_write_certificate 8
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 8) (@Eref VarOrder.T (@Eid VarOrder.T 42))) generated_module_2_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_628_sync : node_sync_check generated_modules multiplier_instances [::14] 8 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_628_type invalid snapshot final initial
 (initial_found:circuit_lookup [::14] 8 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::14] 8 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=42).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_628_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_628_sync.
 - exact ran.
Qed.
Lemma global_scalar_628_step invalid snapshot final v initial
 (source_found:circuit_lookup [::14] 42 snapshot=Some(Gval (Fuint 1) (global_word_627 v)))
 (initial_found:circuit_lookup [::14] 8 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_627 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_628 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::14] 8 final=Some(Gval (Fuint 1) (global_word_628 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=42).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_628_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_628_sync.
 - exact ran.
Qed.
Lemma global_scalar_632_syntax : framed_write_certificate 6
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 6) (@Eref VarOrder.T (@Eid VarOrder.T 34))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_632_sync : node_sync_check generated_modules multiplier_instances [::11;14] 6 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_632_type invalid snapshot final initial
 (initial_found:circuit_lookup [::11;14] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::11;14] 6 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_632_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_632_sync.
 - exact ran.
Qed.
Lemma global_scalar_632_step invalid snapshot final v initial
 (source_found:circuit_lookup [::11;14] 34 snapshot=Some(Gval (Fuint 1) (global_word_631 v)))
 (initial_found:circuit_lookup [::11;14] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_631 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_632 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;14] 6 final=Some(Gval (Fuint 1) (global_word_632 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_632_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_632_sync.
 - exact ran.
Qed.
Lemma global_scalar_635_syntax : framed_write_certificate 9
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 9) (@Eref VarOrder.T (@Eid VarOrder.T 43))) generated_module_2_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_635_sync : node_sync_check generated_modules multiplier_instances [::14] 9 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_635_type invalid snapshot final initial
 (initial_found:circuit_lookup [::14] 9 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::14] 9 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=43).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_635_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_635_sync.
 - exact ran.
Qed.
Lemma global_scalar_635_step invalid snapshot final v initial
 (source_found:circuit_lookup [::14] 43 snapshot=Some(Gval (Fuint 1) (global_word_634 v)))
 (initial_found:circuit_lookup [::14] 9 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_634 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_635 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::14] 9 final=Some(Gval (Fuint 1) (global_word_635 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=43).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_635_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_635_sync.
 - exact ran.
Qed.
Lemma global_scalar_667_syntax : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 33))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_667_sync : node_sync_check generated_modules multiplier_instances [::10;15] 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_667_type invalid snapshot final initial
 (initial_found:circuit_lookup [::10;15] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::10;15] 5 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_667_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_667_sync.
 - exact ran.
Qed.
Lemma global_scalar_667_step invalid snapshot final v initial
 (source_found:circuit_lookup [::10;15] 33 snapshot=Some(Gval (Fuint 1) (global_word_666 v)))
 (initial_found:circuit_lookup [::10;15] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_666 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_667 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;15] 5 final=Some(Gval (Fuint 1) (global_word_667 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_667_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_667_sync.
 - exact ran.
Qed.
Lemma global_scalar_687_syntax : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 33))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_687_sync : node_sync_check generated_modules multiplier_instances [::11;15] 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_687_type invalid snapshot final initial
 (initial_found:circuit_lookup [::11;15] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::11;15] 5 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_687_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_687_sync.
 - exact ran.
Qed.
Lemma global_scalar_687_step invalid snapshot final v initial
 (source_found:circuit_lookup [::11;15] 33 snapshot=Some(Gval (Fuint 1) (global_word_686 v)))
 (initial_found:circuit_lookup [::11;15] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_686 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_687 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;15] 5 final=Some(Gval (Fuint 1) (global_word_687 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_687_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_687_sync.
 - exact ran.
Qed.
Lemma global_scalar_690_syntax : framed_write_certificate 7
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 7) (@Eref VarOrder.T (@Eid VarOrder.T 41))) generated_module_2_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_690_sync : node_sync_check generated_modules multiplier_instances [::15] 7 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_690_type invalid snapshot final initial
 (initial_found:circuit_lookup [::15] 7 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::15] 7 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=41).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_690_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_690_sync.
 - exact ran.
Qed.
Lemma global_scalar_690_step invalid snapshot final v initial
 (source_found:circuit_lookup [::15] 41 snapshot=Some(Gval (Fuint 1) (global_word_689 v)))
 (initial_found:circuit_lookup [::15] 7 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_689 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_690 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::15] 7 final=Some(Gval (Fuint 1) (global_word_690 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=41).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_690_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_690_sync.
 - exact ran.
Qed.
Lemma global_scalar_694_syntax : framed_write_certificate 6
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 6) (@Eref VarOrder.T (@Eid VarOrder.T 34))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_694_sync : node_sync_check generated_modules multiplier_instances [::10;15] 6 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_694_type invalid snapshot final initial
 (initial_found:circuit_lookup [::10;15] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::10;15] 6 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_694_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_694_sync.
 - exact ran.
Qed.
Lemma global_scalar_694_step invalid snapshot final v initial
 (source_found:circuit_lookup [::10;15] 34 snapshot=Some(Gval (Fuint 1) (global_word_693 v)))
 (initial_found:circuit_lookup [::10;15] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_693 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_694 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;15] 6 final=Some(Gval (Fuint 1) (global_word_694 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_694_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_694_sync.
 - exact ran.
Qed.
Lemma global_scalar_697_syntax : framed_write_certificate 8
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 8) (@Eref VarOrder.T (@Eid VarOrder.T 42))) generated_module_2_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_697_sync : node_sync_check generated_modules multiplier_instances [::15] 8 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_697_type invalid snapshot final initial
 (initial_found:circuit_lookup [::15] 8 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::15] 8 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=42).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_697_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_697_sync.
 - exact ran.
Qed.
Lemma global_scalar_697_step invalid snapshot final v initial
 (source_found:circuit_lookup [::15] 42 snapshot=Some(Gval (Fuint 1) (global_word_696 v)))
 (initial_found:circuit_lookup [::15] 8 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_696 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_697 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::15] 8 final=Some(Gval (Fuint 1) (global_word_697 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=42).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_697_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_697_sync.
 - exact ran.
Qed.
Lemma global_scalar_701_syntax : framed_write_certificate 6
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 6) (@Eref VarOrder.T (@Eid VarOrder.T 34))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_701_sync : node_sync_check generated_modules multiplier_instances [::11;15] 6 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_701_type invalid snapshot final initial
 (initial_found:circuit_lookup [::11;15] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::11;15] 6 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_701_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_701_sync.
 - exact ran.
Qed.
Lemma global_scalar_701_step invalid snapshot final v initial
 (source_found:circuit_lookup [::11;15] 34 snapshot=Some(Gval (Fuint 1) (global_word_700 v)))
 (initial_found:circuit_lookup [::11;15] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_700 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_701 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;15] 6 final=Some(Gval (Fuint 1) (global_word_701 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_701_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_701_sync.
 - exact ran.
Qed.
Lemma global_scalar_704_syntax : framed_write_certificate 9
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 9) (@Eref VarOrder.T (@Eid VarOrder.T 43))) generated_module_2_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_704_sync : node_sync_check generated_modules multiplier_instances [::15] 9 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_704_type invalid snapshot final initial
 (initial_found:circuit_lookup [::15] 9 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::15] 9 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=43).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_704_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_704_sync.
 - exact ran.
Qed.
Lemma global_scalar_704_step invalid snapshot final v initial
 (source_found:circuit_lookup [::15] 43 snapshot=Some(Gval (Fuint 1) (global_word_703 v)))
 (initial_found:circuit_lookup [::15] 9 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_703 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_704 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::15] 9 final=Some(Gval (Fuint 1) (global_word_704 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=43).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_704_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_704_sync.
 - exact ran.
Qed.
Lemma global_scalar_736_syntax : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 33))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_736_sync : node_sync_check generated_modules multiplier_instances [::10;16] 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_736_type invalid snapshot final initial
 (initial_found:circuit_lookup [::10;16] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::10;16] 5 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_736_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_736_sync.
 - exact ran.
Qed.
Lemma global_scalar_736_step invalid snapshot final v initial
 (source_found:circuit_lookup [::10;16] 33 snapshot=Some(Gval (Fuint 1) (global_word_735 v)))
 (initial_found:circuit_lookup [::10;16] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_735 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_736 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 5 final=Some(Gval (Fuint 1) (global_word_736 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_736_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_736_sync.
 - exact ran.
Qed.
Lemma global_scalar_756_syntax : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 33))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_756_sync : node_sync_check generated_modules multiplier_instances [::11;16] 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_756_type invalid snapshot final initial
 (initial_found:circuit_lookup [::11;16] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::11;16] 5 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_756_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_756_sync.
 - exact ran.
Qed.
Lemma global_scalar_756_step invalid snapshot final v initial
 (source_found:circuit_lookup [::11;16] 33 snapshot=Some(Gval (Fuint 1) (global_word_755 v)))
 (initial_found:circuit_lookup [::11;16] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_755 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_756 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 5 final=Some(Gval (Fuint 1) (global_word_756 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_756_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_756_sync.
 - exact ran.
Qed.
Lemma global_scalar_759_syntax : framed_write_certificate 7
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 7) (@Eref VarOrder.T (@Eid VarOrder.T 41))) generated_module_2_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_759_sync : node_sync_check generated_modules multiplier_instances [::16] 7 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_759_type invalid snapshot final initial
 (initial_found:circuit_lookup [::16] 7 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::16] 7 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=41).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_759_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_759_sync.
 - exact ran.
Qed.
Lemma global_scalar_759_step invalid snapshot final v initial
 (source_found:circuit_lookup [::16] 41 snapshot=Some(Gval (Fuint 1) (global_word_758 v)))
 (initial_found:circuit_lookup [::16] 7 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_758 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_759 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::16] 7 final=Some(Gval (Fuint 1) (global_word_759 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=41).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_759_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_759_sync.
 - exact ran.
Qed.
Lemma global_scalar_763_syntax : framed_write_certificate 6
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 6) (@Eref VarOrder.T (@Eid VarOrder.T 34))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_763_sync : node_sync_check generated_modules multiplier_instances [::10;16] 6 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_763_type invalid snapshot final initial
 (initial_found:circuit_lookup [::10;16] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::10;16] 6 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_763_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_763_sync.
 - exact ran.
Qed.
Lemma global_scalar_763_step invalid snapshot final v initial
 (source_found:circuit_lookup [::10;16] 34 snapshot=Some(Gval (Fuint 1) (global_word_762 v)))
 (initial_found:circuit_lookup [::10;16] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_762 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_763 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 6 final=Some(Gval (Fuint 1) (global_word_763 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_763_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_763_sync.
 - exact ran.
Qed.
Lemma global_scalar_766_syntax : framed_write_certificate 8
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 8) (@Eref VarOrder.T (@Eid VarOrder.T 42))) generated_module_2_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_766_sync : node_sync_check generated_modules multiplier_instances [::16] 8 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_766_type invalid snapshot final initial
 (initial_found:circuit_lookup [::16] 8 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::16] 8 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=42).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_766_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_766_sync.
 - exact ran.
Qed.
Lemma global_scalar_766_step invalid snapshot final v initial
 (source_found:circuit_lookup [::16] 42 snapshot=Some(Gval (Fuint 1) (global_word_765 v)))
 (initial_found:circuit_lookup [::16] 8 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_765 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_766 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::16] 8 final=Some(Gval (Fuint 1) (global_word_766 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=42).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_766_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_766_sync.
 - exact ran.
Qed.
Lemma global_scalar_770_syntax : framed_write_certificate 6
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 6) (@Eref VarOrder.T (@Eid VarOrder.T 34))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_770_sync : node_sync_check generated_modules multiplier_instances [::11;16] 6 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_770_type invalid snapshot final initial
 (initial_found:circuit_lookup [::11;16] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::11;16] 6 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_770_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_770_sync.
 - exact ran.
Qed.
Lemma global_scalar_770_step invalid snapshot final v initial
 (source_found:circuit_lookup [::11;16] 34 snapshot=Some(Gval (Fuint 1) (global_word_769 v)))
 (initial_found:circuit_lookup [::11;16] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_769 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_770 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 6 final=Some(Gval (Fuint 1) (global_word_770 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_770_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_770_sync.
 - exact ran.
Qed.
Lemma global_scalar_773_syntax : framed_write_certificate 9
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 9) (@Eref VarOrder.T (@Eid VarOrder.T 43))) generated_module_2_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_773_sync : node_sync_check generated_modules multiplier_instances [::16] 9 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_773_type invalid snapshot final initial
 (initial_found:circuit_lookup [::16] 9 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::16] 9 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=43).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_773_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_773_sync.
 - exact ran.
Qed.
Lemma global_scalar_773_step invalid snapshot final v initial
 (source_found:circuit_lookup [::16] 43 snapshot=Some(Gval (Fuint 1) (global_word_772 v)))
 (initial_found:circuit_lookup [::16] 9 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_772 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_773 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::16] 9 final=Some(Gval (Fuint 1) (global_word_773 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=43).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_773_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_773_sync.
 - exact ran.
Qed.
Lemma global_scalar_805_syntax : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 33))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_805_sync : node_sync_check generated_modules multiplier_instances [::10;17] 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_805_type invalid snapshot final initial
 (initial_found:circuit_lookup [::10;17] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::10;17] 5 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_805_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_805_sync.
 - exact ran.
Qed.
Lemma global_scalar_805_step invalid snapshot final v initial
 (source_found:circuit_lookup [::10;17] 33 snapshot=Some(Gval (Fuint 1) (global_word_804 v)))
 (initial_found:circuit_lookup [::10;17] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_804 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_805 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 5 final=Some(Gval (Fuint 1) (global_word_805 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_805_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_805_sync.
 - exact ran.
Qed.
Lemma global_scalar_825_syntax : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 33))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_825_sync : node_sync_check generated_modules multiplier_instances [::11;17] 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_825_type invalid snapshot final initial
 (initial_found:circuit_lookup [::11;17] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::11;17] 5 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_825_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_825_sync.
 - exact ran.
Qed.
Lemma global_scalar_825_step invalid snapshot final v initial
 (source_found:circuit_lookup [::11;17] 33 snapshot=Some(Gval (Fuint 1) (global_word_824 v)))
 (initial_found:circuit_lookup [::11;17] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_824 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_825 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 5 final=Some(Gval (Fuint 1) (global_word_825 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_825_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_825_sync.
 - exact ran.
Qed.
Lemma global_scalar_828_syntax : framed_write_certificate 7
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 7) (@Eref VarOrder.T (@Eid VarOrder.T 41))) generated_module_2_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_828_sync : node_sync_check generated_modules multiplier_instances [::17] 7 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_828_type invalid snapshot final initial
 (initial_found:circuit_lookup [::17] 7 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::17] 7 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=41).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_828_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_828_sync.
 - exact ran.
Qed.
Lemma global_scalar_828_step invalid snapshot final v initial
 (source_found:circuit_lookup [::17] 41 snapshot=Some(Gval (Fuint 1) (global_word_827 v)))
 (initial_found:circuit_lookup [::17] 7 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_827 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_828 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 7 final=Some(Gval (Fuint 1) (global_word_828 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=41).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_828_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_828_sync.
 - exact ran.
Qed.
Lemma global_scalar_832_syntax : framed_write_certificate 6
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 6) (@Eref VarOrder.T (@Eid VarOrder.T 34))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_832_sync : node_sync_check generated_modules multiplier_instances [::10;17] 6 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_832_type invalid snapshot final initial
 (initial_found:circuit_lookup [::10;17] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::10;17] 6 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_832_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_832_sync.
 - exact ran.
Qed.
Lemma global_scalar_832_step invalid snapshot final v initial
 (source_found:circuit_lookup [::10;17] 34 snapshot=Some(Gval (Fuint 1) (global_word_831 v)))
 (initial_found:circuit_lookup [::10;17] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_831 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_832 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 6 final=Some(Gval (Fuint 1) (global_word_832 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_832_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_832_sync.
 - exact ran.
Qed.
Lemma global_scalar_835_syntax : framed_write_certificate 8
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 8) (@Eref VarOrder.T (@Eid VarOrder.T 42))) generated_module_2_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_835_sync : node_sync_check generated_modules multiplier_instances [::17] 8 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_835_type invalid snapshot final initial
 (initial_found:circuit_lookup [::17] 8 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::17] 8 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=42).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_835_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_835_sync.
 - exact ran.
Qed.
Lemma global_scalar_835_step invalid snapshot final v initial
 (source_found:circuit_lookup [::17] 42 snapshot=Some(Gval (Fuint 1) (global_word_834 v)))
 (initial_found:circuit_lookup [::17] 8 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_834 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_835 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 8 final=Some(Gval (Fuint 1) (global_word_835 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=42).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_835_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_835_sync.
 - exact ran.
Qed.
Lemma global_scalar_839_syntax : framed_write_certificate 6
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 6) (@Eref VarOrder.T (@Eid VarOrder.T 34))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_839_sync : node_sync_check generated_modules multiplier_instances [::11;17] 6 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_839_type invalid snapshot final initial
 (initial_found:circuit_lookup [::11;17] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::11;17] 6 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_839_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_839_sync.
 - exact ran.
Qed.
Lemma global_scalar_839_step invalid snapshot final v initial
 (source_found:circuit_lookup [::11;17] 34 snapshot=Some(Gval (Fuint 1) (global_word_838 v)))
 (initial_found:circuit_lookup [::11;17] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_838 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_839 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 6 final=Some(Gval (Fuint 1) (global_word_839 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_839_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_839_sync.
 - exact ran.
Qed.
Lemma global_scalar_842_syntax : framed_write_certificate 9
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 9) (@Eref VarOrder.T (@Eid VarOrder.T 43))) generated_module_2_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_842_sync : node_sync_check generated_modules multiplier_instances [::17] 9 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_842_type invalid snapshot final initial
 (initial_found:circuit_lookup [::17] 9 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::17] 9 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=43).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_842_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_842_sync.
 - exact ran.
Qed.
Lemma global_scalar_842_step invalid snapshot final v initial
 (source_found:circuit_lookup [::17] 43 snapshot=Some(Gval (Fuint 1) (global_word_841 v)))
 (initial_found:circuit_lookup [::17] 9 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_841 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_842 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 9 final=Some(Gval (Fuint 1) (global_word_842 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=43).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_842_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_842_sync.
 - exact ran.
Qed.
Lemma global_scalar_874_syntax : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 33))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_874_sync : node_sync_check generated_modules multiplier_instances [::10;18] 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_874_type invalid snapshot final initial
 (initial_found:circuit_lookup [::10;18] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::10;18] 5 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_874_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_874_sync.
 - exact ran.
Qed.
Lemma global_scalar_874_step invalid snapshot final v initial
 (source_found:circuit_lookup [::10;18] 33 snapshot=Some(Gval (Fuint 1) (global_word_873 v)))
 (initial_found:circuit_lookup [::10;18] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_873 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_874 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 5 final=Some(Gval (Fuint 1) (global_word_874 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_874_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_874_sync.
 - exact ran.
Qed.
Lemma global_scalar_894_syntax : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 33))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_894_sync : node_sync_check generated_modules multiplier_instances [::11;18] 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_894_type invalid snapshot final initial
 (initial_found:circuit_lookup [::11;18] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::11;18] 5 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_894_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_894_sync.
 - exact ran.
Qed.
Lemma global_scalar_894_step invalid snapshot final v initial
 (source_found:circuit_lookup [::11;18] 33 snapshot=Some(Gval (Fuint 1) (global_word_893 v)))
 (initial_found:circuit_lookup [::11;18] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_893 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_894 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 5 final=Some(Gval (Fuint 1) (global_word_894 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_894_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_894_sync.
 - exact ran.
Qed.
Lemma global_scalar_897_syntax : framed_write_certificate 7
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 7) (@Eref VarOrder.T (@Eid VarOrder.T 41))) generated_module_2_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_897_sync : node_sync_check generated_modules multiplier_instances [::18] 7 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_897_type invalid snapshot final initial
 (initial_found:circuit_lookup [::18] 7 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::18] 7 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=41).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_897_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_897_sync.
 - exact ran.
Qed.
Lemma global_scalar_897_step invalid snapshot final v initial
 (source_found:circuit_lookup [::18] 41 snapshot=Some(Gval (Fuint 1) (global_word_896 v)))
 (initial_found:circuit_lookup [::18] 7 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_896 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_897 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 7 final=Some(Gval (Fuint 1) (global_word_897 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=41).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_897_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_897_sync.
 - exact ran.
Qed.
Lemma global_scalar_901_syntax : framed_write_certificate 6
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 6) (@Eref VarOrder.T (@Eid VarOrder.T 34))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_901_sync : node_sync_check generated_modules multiplier_instances [::10;18] 6 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_901_type invalid snapshot final initial
 (initial_found:circuit_lookup [::10;18] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::10;18] 6 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_901_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_901_sync.
 - exact ran.
Qed.
Lemma global_scalar_901_step invalid snapshot final v initial
 (source_found:circuit_lookup [::10;18] 34 snapshot=Some(Gval (Fuint 1) (global_word_900 v)))
 (initial_found:circuit_lookup [::10;18] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_900 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_901 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 6 final=Some(Gval (Fuint 1) (global_word_901 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_901_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_901_sync.
 - exact ran.
Qed.
Lemma global_scalar_904_syntax : framed_write_certificate 8
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 8) (@Eref VarOrder.T (@Eid VarOrder.T 42))) generated_module_2_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_904_sync : node_sync_check generated_modules multiplier_instances [::18] 8 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_904_type invalid snapshot final initial
 (initial_found:circuit_lookup [::18] 8 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::18] 8 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=42).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_904_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_904_sync.
 - exact ran.
Qed.
Lemma global_scalar_904_step invalid snapshot final v initial
 (source_found:circuit_lookup [::18] 42 snapshot=Some(Gval (Fuint 1) (global_word_903 v)))
 (initial_found:circuit_lookup [::18] 8 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_903 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_904 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 8 final=Some(Gval (Fuint 1) (global_word_904 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=42).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_904_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_904_sync.
 - exact ran.
Qed.
Lemma global_scalar_908_syntax : framed_write_certificate 6
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 6) (@Eref VarOrder.T (@Eid VarOrder.T 34))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_908_sync : node_sync_check generated_modules multiplier_instances [::11;18] 6 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_908_type invalid snapshot final initial
 (initial_found:circuit_lookup [::11;18] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::11;18] 6 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_908_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_908_sync.
 - exact ran.
Qed.
Lemma global_scalar_908_step invalid snapshot final v initial
 (source_found:circuit_lookup [::11;18] 34 snapshot=Some(Gval (Fuint 1) (global_word_907 v)))
 (initial_found:circuit_lookup [::11;18] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_907 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_908 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 6 final=Some(Gval (Fuint 1) (global_word_908 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_908_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_908_sync.
 - exact ran.
Qed.
Lemma global_scalar_911_syntax : framed_write_certificate 9
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 9) (@Eref VarOrder.T (@Eid VarOrder.T 43))) generated_module_2_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_911_sync : node_sync_check generated_modules multiplier_instances [::18] 9 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_911_type invalid snapshot final initial
 (initial_found:circuit_lookup [::18] 9 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::18] 9 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=43).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_911_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_911_sync.
 - exact ran.
Qed.
Lemma global_scalar_911_step invalid snapshot final v initial
 (source_found:circuit_lookup [::18] 43 snapshot=Some(Gval (Fuint 1) (global_word_910 v)))
 (initial_found:circuit_lookup [::18] 9 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_910 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_911 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 9 final=Some(Gval (Fuint 1) (global_word_911 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=2) (ports:=multiplier_ports 2) (stmts:=generated_module_2_stmts_0) (source:=43).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_911_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_911_sync.
 - exact ran.
Qed.
Lemma global_scalar_931_syntax : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 33))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_931_sync : node_sync_check generated_modules multiplier_instances [::19] 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_931_type invalid snapshot final initial
 (initial_found:circuit_lookup [::19] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::19] 5 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_931_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_931_sync.
 - exact ran.
Qed.
Lemma global_scalar_931_step invalid snapshot final v initial
 (source_found:circuit_lookup [::19] 33 snapshot=Some(Gval (Fuint 1) (global_word_930 v)))
 (initial_found:circuit_lookup [::19] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_930 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_931 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 5 final=Some(Gval (Fuint 1) (global_word_931 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_931_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_931_sync.
 - exact ran.
Qed.
Lemma global_scalar_935_syntax : framed_write_certificate 6
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 6) (@Eref VarOrder.T (@Eid VarOrder.T 34))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_935_sync : node_sync_check generated_modules multiplier_instances [::19] 6 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_935_type invalid snapshot final initial
 (initial_found:circuit_lookup [::19] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::19] 6 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_935_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_935_sync.
 - exact ran.
Qed.
Lemma global_scalar_935_step invalid snapshot final v initial
 (source_found:circuit_lookup [::19] 34 snapshot=Some(Gval (Fuint 1) (global_word_934 v)))
 (initial_found:circuit_lookup [::19] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_934 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_935 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 6 final=Some(Gval (Fuint 1) (global_word_935 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_935_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_935_sync.
 - exact ran.
Qed.
Lemma global_scalar_949_syntax : framed_write_certificate 4
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 4) (@Eref VarOrder.T (@Eid VarOrder.T 25))) generated_module_0_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_949_sync : node_sync_check generated_modules multiplier_instances [::20] 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_949_type invalid snapshot final initial
 (initial_found:circuit_lookup [::20] 4 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::20] 4 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=25).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_949_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_949_sync.
 - exact ran.
Qed.
Lemma global_scalar_949_step invalid snapshot final v initial
 (source_found:circuit_lookup [::20] 25 snapshot=Some(Gval (Fuint 1) (global_word_948 v)))
 (initial_found:circuit_lookup [::20] 4 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_948 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_949 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::20] 4 final=Some(Gval (Fuint 1) (global_word_949 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=25).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_949_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_949_sync.
 - exact ran.
Qed.
Lemma global_scalar_953_syntax : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 26))) generated_module_0_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_953_sync : node_sync_check generated_modules multiplier_instances [::20] 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_953_type invalid snapshot final initial
 (initial_found:circuit_lookup [::20] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::20] 5 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=26).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_953_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_953_sync.
 - exact ran.
Qed.
Lemma global_scalar_953_step invalid snapshot final v initial
 (source_found:circuit_lookup [::20] 26 snapshot=Some(Gval (Fuint 1) (global_word_952 v)))
 (initial_found:circuit_lookup [::20] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_952 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_953 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::20] 5 final=Some(Gval (Fuint 1) (global_word_953 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=26).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_953_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_953_sync.
 - exact ran.
Qed.
Lemma global_scalar_967_syntax : framed_write_certificate 4
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 4) (@Eref VarOrder.T (@Eid VarOrder.T 25))) generated_module_0_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_967_sync : node_sync_check generated_modules multiplier_instances [::21] 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_967_type invalid snapshot final initial
 (initial_found:circuit_lookup [::21] 4 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::21] 4 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=25).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_967_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_967_sync.
 - exact ran.
Qed.
Lemma global_scalar_967_step invalid snapshot final v initial
 (source_found:circuit_lookup [::21] 25 snapshot=Some(Gval (Fuint 1) (global_word_966 v)))
 (initial_found:circuit_lookup [::21] 4 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_966 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_967 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::21] 4 final=Some(Gval (Fuint 1) (global_word_967 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=25).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_967_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_967_sync.
 - exact ran.
Qed.
Lemma global_scalar_971_syntax : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 26))) generated_module_0_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_971_sync : node_sync_check generated_modules multiplier_instances [::21] 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_971_type invalid snapshot final initial
 (initial_found:circuit_lookup [::21] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::21] 5 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=26).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_971_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_971_sync.
 - exact ran.
Qed.
Lemma global_scalar_971_step invalid snapshot final v initial
 (source_found:circuit_lookup [::21] 26 snapshot=Some(Gval (Fuint 1) (global_word_970 v)))
 (initial_found:circuit_lookup [::21] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_970 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_971 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::21] 5 final=Some(Gval (Fuint 1) (global_word_971 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=26).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_971_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_971_sync.
 - exact ran.
Qed.
Lemma global_scalar_985_syntax : framed_write_certificate 4
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 4) (@Eref VarOrder.T (@Eid VarOrder.T 25))) generated_module_0_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_985_sync : node_sync_check generated_modules multiplier_instances [::22] 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_985_type invalid snapshot final initial
 (initial_found:circuit_lookup [::22] 4 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::22] 4 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=25).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_985_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_985_sync.
 - exact ran.
Qed.
Lemma global_scalar_985_step invalid snapshot final v initial
 (source_found:circuit_lookup [::22] 25 snapshot=Some(Gval (Fuint 1) (global_word_984 v)))
 (initial_found:circuit_lookup [::22] 4 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_984 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_985 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::22] 4 final=Some(Gval (Fuint 1) (global_word_985 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=25).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_985_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_985_sync.
 - exact ran.
Qed.
Lemma global_scalar_989_syntax : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 26))) generated_module_0_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_989_sync : node_sync_check generated_modules multiplier_instances [::22] 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_989_type invalid snapshot final initial
 (initial_found:circuit_lookup [::22] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::22] 5 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=26).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_989_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_989_sync.
 - exact ran.
Qed.
Lemma global_scalar_989_step invalid snapshot final v initial
 (source_found:circuit_lookup [::22] 26 snapshot=Some(Gval (Fuint 1) (global_word_988 v)))
 (initial_found:circuit_lookup [::22] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_988 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_989 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::22] 5 final=Some(Gval (Fuint 1) (global_word_989 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=26).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_989_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_989_sync.
 - exact ran.
Qed.
Lemma global_scalar_1003_syntax : framed_write_certificate 4
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 4) (@Eref VarOrder.T (@Eid VarOrder.T 25))) generated_module_0_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_1003_sync : node_sync_check generated_modules multiplier_instances [::23] 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_1003_type invalid snapshot final initial
 (initial_found:circuit_lookup [::23] 4 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::23] 4 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=25).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1003_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_1003_sync.
 - exact ran.
Qed.
Lemma global_scalar_1003_step invalid snapshot final v initial
 (source_found:circuit_lookup [::23] 25 snapshot=Some(Gval (Fuint 1) (global_word_1002 v)))
 (initial_found:circuit_lookup [::23] 4 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1002 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_1003 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::23] 4 final=Some(Gval (Fuint 1) (global_word_1003 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=25).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1003_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_1003_sync.
 - exact ran.
Qed.
Lemma global_scalar_1007_syntax : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 26))) generated_module_0_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_1007_sync : node_sync_check generated_modules multiplier_instances [::23] 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_1007_type invalid snapshot final initial
 (initial_found:circuit_lookup [::23] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::23] 5 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=26).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1007_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_1007_sync.
 - exact ran.
Qed.
Lemma global_scalar_1007_step invalid snapshot final v initial
 (source_found:circuit_lookup [::23] 26 snapshot=Some(Gval (Fuint 1) (global_word_1006 v)))
 (initial_found:circuit_lookup [::23] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1006 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_1007 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::23] 5 final=Some(Gval (Fuint 1) (global_word_1007 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=26).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1007_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_1007_sync.
 - exact ran.
Qed.
Lemma global_scalar_1021_syntax : framed_write_certificate 4
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 4) (@Eref VarOrder.T (@Eid VarOrder.T 25))) generated_module_0_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_1021_sync : node_sync_check generated_modules multiplier_instances [::24] 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_1021_type invalid snapshot final initial
 (initial_found:circuit_lookup [::24] 4 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::24] 4 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=25).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1021_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_1021_sync.
 - exact ran.
Qed.
Lemma global_scalar_1021_step invalid snapshot final v initial
 (source_found:circuit_lookup [::24] 25 snapshot=Some(Gval (Fuint 1) (global_word_1020 v)))
 (initial_found:circuit_lookup [::24] 4 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1020 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_1021 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::24] 4 final=Some(Gval (Fuint 1) (global_word_1021 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=25).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1021_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_1021_sync.
 - exact ran.
Qed.
Lemma global_scalar_1025_syntax : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 26))) generated_module_0_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_1025_sync : node_sync_check generated_modules multiplier_instances [::24] 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_1025_type invalid snapshot final initial
 (initial_found:circuit_lookup [::24] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::24] 5 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=26).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1025_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_1025_sync.
 - exact ran.
Qed.
Lemma global_scalar_1025_step invalid snapshot final v initial
 (source_found:circuit_lookup [::24] 26 snapshot=Some(Gval (Fuint 1) (global_word_1024 v)))
 (initial_found:circuit_lookup [::24] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1024 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_1025 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::24] 5 final=Some(Gval (Fuint 1) (global_word_1025 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=26).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1025_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_1025_sync.
 - exact ran.
Qed.
Lemma global_scalar_1039_syntax : framed_write_certificate 4
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 4) (@Eref VarOrder.T (@Eid VarOrder.T 25))) generated_module_0_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_1039_sync : node_sync_check generated_modules multiplier_instances [::25] 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_1039_type invalid snapshot final initial
 (initial_found:circuit_lookup [::25] 4 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::25] 4 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=25).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1039_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_1039_sync.
 - exact ran.
Qed.
Lemma global_scalar_1039_step invalid snapshot final v initial
 (source_found:circuit_lookup [::25] 25 snapshot=Some(Gval (Fuint 1) (global_word_1038 v)))
 (initial_found:circuit_lookup [::25] 4 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1038 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_1039 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::25] 4 final=Some(Gval (Fuint 1) (global_word_1039 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=25).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1039_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_1039_sync.
 - exact ran.
Qed.
Lemma global_scalar_1043_syntax : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 26))) generated_module_0_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_1043_sync : node_sync_check generated_modules multiplier_instances [::25] 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_1043_type invalid snapshot final initial
 (initial_found:circuit_lookup [::25] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::25] 5 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=26).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1043_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_1043_sync.
 - exact ran.
Qed.
Lemma global_scalar_1043_step invalid snapshot final v initial
 (source_found:circuit_lookup [::25] 26 snapshot=Some(Gval (Fuint 1) (global_word_1042 v)))
 (initial_found:circuit_lookup [::25] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1042 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_1043 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::25] 5 final=Some(Gval (Fuint 1) (global_word_1043 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=26).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1043_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_1043_sync.
 - exact ran.
Qed.
Lemma global_scalar_1057_syntax : framed_write_certificate 4
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 4) (@Eref VarOrder.T (@Eid VarOrder.T 25))) generated_module_0_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_1057_sync : node_sync_check generated_modules multiplier_instances [::26] 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_1057_type invalid snapshot final initial
 (initial_found:circuit_lookup [::26] 4 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::26] 4 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=25).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1057_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_1057_sync.
 - exact ran.
Qed.
Lemma global_scalar_1057_step invalid snapshot final v initial
 (source_found:circuit_lookup [::26] 25 snapshot=Some(Gval (Fuint 1) (global_word_1056 v)))
 (initial_found:circuit_lookup [::26] 4 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1056 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_1057 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::26] 4 final=Some(Gval (Fuint 1) (global_word_1057 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=25).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1057_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_1057_sync.
 - exact ran.
Qed.
Lemma global_scalar_1061_syntax : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 26))) generated_module_0_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_1061_sync : node_sync_check generated_modules multiplier_instances [::26] 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_1061_type invalid snapshot final initial
 (initial_found:circuit_lookup [::26] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::26] 5 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=26).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1061_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_1061_sync.
 - exact ran.
Qed.
Lemma global_scalar_1061_step invalid snapshot final v initial
 (source_found:circuit_lookup [::26] 26 snapshot=Some(Gval (Fuint 1) (global_word_1060 v)))
 (initial_found:circuit_lookup [::26] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1060 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_1061 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::26] 5 final=Some(Gval (Fuint 1) (global_word_1061 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=26).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1061_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_1061_sync.
 - exact ran.
Qed.
Lemma global_scalar_1081_syntax : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 33))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_1081_sync : node_sync_check generated_modules multiplier_instances [::27] 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_1081_type invalid snapshot final initial
 (initial_found:circuit_lookup [::27] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::27] 5 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1081_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_1081_sync.
 - exact ran.
Qed.
Lemma global_scalar_1081_step invalid snapshot final v initial
 (source_found:circuit_lookup [::27] 33 snapshot=Some(Gval (Fuint 1) (global_word_1080 v)))
 (initial_found:circuit_lookup [::27] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1080 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_1081 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 5 final=Some(Gval (Fuint 1) (global_word_1081 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1081_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_1081_sync.
 - exact ran.
Qed.
Lemma global_scalar_1085_syntax : framed_write_certificate 6
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 6) (@Eref VarOrder.T (@Eid VarOrder.T 34))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_1085_sync : node_sync_check generated_modules multiplier_instances [::27] 6 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_1085_type invalid snapshot final initial
 (initial_found:circuit_lookup [::27] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::27] 6 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1085_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_1085_sync.
 - exact ran.
Qed.
Lemma global_scalar_1085_step invalid snapshot final v initial
 (source_found:circuit_lookup [::27] 34 snapshot=Some(Gval (Fuint 1) (global_word_1084 v)))
 (initial_found:circuit_lookup [::27] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1084 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_1085 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 6 final=Some(Gval (Fuint 1) (global_word_1085 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1085_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_1085_sync.
 - exact ran.
Qed.
Lemma global_scalar_1105_syntax : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 33))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_1105_sync : node_sync_check generated_modules multiplier_instances [::28] 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_1105_type invalid snapshot final initial
 (initial_found:circuit_lookup [::28] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::28] 5 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1105_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_1105_sync.
 - exact ran.
Qed.
Lemma global_scalar_1105_step invalid snapshot final v initial
 (source_found:circuit_lookup [::28] 33 snapshot=Some(Gval (Fuint 1) (global_word_1104 v)))
 (initial_found:circuit_lookup [::28] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1104 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_1105 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 5 final=Some(Gval (Fuint 1) (global_word_1105 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1105_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_1105_sync.
 - exact ran.
Qed.
Lemma global_scalar_1109_syntax : framed_write_certificate 6
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 6) (@Eref VarOrder.T (@Eid VarOrder.T 34))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_1109_sync : node_sync_check generated_modules multiplier_instances [::28] 6 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_1109_type invalid snapshot final initial
 (initial_found:circuit_lookup [::28] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::28] 6 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1109_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_1109_sync.
 - exact ran.
Qed.
Lemma global_scalar_1109_step invalid snapshot final v initial
 (source_found:circuit_lookup [::28] 34 snapshot=Some(Gval (Fuint 1) (global_word_1108 v)))
 (initial_found:circuit_lookup [::28] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1108 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_1109 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 6 final=Some(Gval (Fuint 1) (global_word_1109 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1109_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_1109_sync.
 - exact ran.
Qed.
Lemma global_scalar_1123_syntax : framed_write_certificate 4
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 4) (@Eref VarOrder.T (@Eid VarOrder.T 25))) generated_module_0_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_1123_sync : node_sync_check generated_modules multiplier_instances [::29] 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_1123_type invalid snapshot final initial
 (initial_found:circuit_lookup [::29] 4 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::29] 4 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=25).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1123_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_1123_sync.
 - exact ran.
Qed.
Lemma global_scalar_1123_step invalid snapshot final v initial
 (source_found:circuit_lookup [::29] 25 snapshot=Some(Gval (Fuint 1) (global_word_1122 v)))
 (initial_found:circuit_lookup [::29] 4 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1122 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_1123 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::29] 4 final=Some(Gval (Fuint 1) (global_word_1123 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=25).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1123_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_1123_sync.
 - exact ran.
Qed.
Lemma global_scalar_1127_syntax : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 26))) generated_module_0_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_1127_sync : node_sync_check generated_modules multiplier_instances [::29] 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_1127_type invalid snapshot final initial
 (initial_found:circuit_lookup [::29] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::29] 5 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=26).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1127_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_1127_sync.
 - exact ran.
Qed.
Lemma global_scalar_1127_step invalid snapshot final v initial
 (source_found:circuit_lookup [::29] 26 snapshot=Some(Gval (Fuint 1) (global_word_1126 v)))
 (initial_found:circuit_lookup [::29] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1126 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_1127 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::29] 5 final=Some(Gval (Fuint 1) (global_word_1127 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=26).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1127_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_1127_sync.
 - exact ran.
Qed.
Lemma global_scalar_1141_syntax : framed_write_certificate 4
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 4) (@Eref VarOrder.T (@Eid VarOrder.T 25))) generated_module_0_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_1141_sync : node_sync_check generated_modules multiplier_instances [::30] 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_1141_type invalid snapshot final initial
 (initial_found:circuit_lookup [::30] 4 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::30] 4 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=25).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1141_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_1141_sync.
 - exact ran.
Qed.
Lemma global_scalar_1141_step invalid snapshot final v initial
 (source_found:circuit_lookup [::30] 25 snapshot=Some(Gval (Fuint 1) (global_word_1140 v)))
 (initial_found:circuit_lookup [::30] 4 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1140 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_1141 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::30] 4 final=Some(Gval (Fuint 1) (global_word_1141 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=25).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1141_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_1141_sync.
 - exact ran.
Qed.
Lemma global_scalar_1145_syntax : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 26))) generated_module_0_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_1145_sync : node_sync_check generated_modules multiplier_instances [::30] 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_1145_type invalid snapshot final initial
 (initial_found:circuit_lookup [::30] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::30] 5 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=26).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1145_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_1145_sync.
 - exact ran.
Qed.
Lemma global_scalar_1145_step invalid snapshot final v initial
 (source_found:circuit_lookup [::30] 26 snapshot=Some(Gval (Fuint 1) (global_word_1144 v)))
 (initial_found:circuit_lookup [::30] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1144 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_1145 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::30] 5 final=Some(Gval (Fuint 1) (global_word_1145 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=26).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1145_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_1145_sync.
 - exact ran.
Qed.
Lemma global_scalar_1159_syntax : framed_write_certificate 4
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 4) (@Eref VarOrder.T (@Eid VarOrder.T 25))) generated_module_0_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_1159_sync : node_sync_check generated_modules multiplier_instances [::31] 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_1159_type invalid snapshot final initial
 (initial_found:circuit_lookup [::31] 4 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::31] 4 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=25).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1159_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_1159_sync.
 - exact ran.
Qed.
Lemma global_scalar_1159_step invalid snapshot final v initial
 (source_found:circuit_lookup [::31] 25 snapshot=Some(Gval (Fuint 1) (global_word_1158 v)))
 (initial_found:circuit_lookup [::31] 4 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1158 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_1159 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::31] 4 final=Some(Gval (Fuint 1) (global_word_1159 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=25).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1159_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_1159_sync.
 - exact ran.
Qed.
Lemma global_scalar_1163_syntax : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 26))) generated_module_0_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_1163_sync : node_sync_check generated_modules multiplier_instances [::31] 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_1163_type invalid snapshot final initial
 (initial_found:circuit_lookup [::31] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::31] 5 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=26).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1163_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_1163_sync.
 - exact ran.
Qed.
Lemma global_scalar_1163_step invalid snapshot final v initial
 (source_found:circuit_lookup [::31] 26 snapshot=Some(Gval (Fuint 1) (global_word_1162 v)))
 (initial_found:circuit_lookup [::31] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1162 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_1163 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::31] 5 final=Some(Gval (Fuint 1) (global_word_1163 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=26).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1163_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_1163_sync.
 - exact ran.
Qed.
Lemma global_scalar_1177_syntax : framed_write_certificate 4
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 4) (@Eref VarOrder.T (@Eid VarOrder.T 25))) generated_module_0_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_1177_sync : node_sync_check generated_modules multiplier_instances [::32] 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_1177_type invalid snapshot final initial
 (initial_found:circuit_lookup [::32] 4 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::32] 4 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=25).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1177_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_1177_sync.
 - exact ran.
Qed.
Lemma global_scalar_1177_step invalid snapshot final v initial
 (source_found:circuit_lookup [::32] 25 snapshot=Some(Gval (Fuint 1) (global_word_1176 v)))
 (initial_found:circuit_lookup [::32] 4 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1176 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_1177 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::32] 4 final=Some(Gval (Fuint 1) (global_word_1177 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=25).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1177_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_1177_sync.
 - exact ran.
Qed.
Lemma global_scalar_1181_syntax : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 26))) generated_module_0_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_1181_sync : node_sync_check generated_modules multiplier_instances [::32] 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_1181_type invalid snapshot final initial
 (initial_found:circuit_lookup [::32] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::32] 5 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=26).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1181_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_1181_sync.
 - exact ran.
Qed.
Lemma global_scalar_1181_step invalid snapshot final v initial
 (source_found:circuit_lookup [::32] 26 snapshot=Some(Gval (Fuint 1) (global_word_1180 v)))
 (initial_found:circuit_lookup [::32] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1180 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_1181 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::32] 5 final=Some(Gval (Fuint 1) (global_word_1181 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=26).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1181_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_1181_sync.
 - exact ran.
Qed.
Lemma global_scalar_1201_syntax : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 33))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_1201_sync : node_sync_check generated_modules multiplier_instances [::33] 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_1201_type invalid snapshot final initial
 (initial_found:circuit_lookup [::33] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::33] 5 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1201_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_1201_sync.
 - exact ran.
Qed.
Lemma global_scalar_1201_step invalid snapshot final v initial
 (source_found:circuit_lookup [::33] 33 snapshot=Some(Gval (Fuint 1) (global_word_1200 v)))
 (initial_found:circuit_lookup [::33] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1200 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_1201 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 5 final=Some(Gval (Fuint 1) (global_word_1201 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=33).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1201_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_1201_sync.
 - exact ran.
Qed.
Lemma global_scalar_1205_syntax : framed_write_certificate 6
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 6) (@Eref VarOrder.T (@Eid VarOrder.T 34))) generated_module_1_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_1205_sync : node_sync_check generated_modules multiplier_instances [::33] 6 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_1205_type invalid snapshot final initial
 (initial_found:circuit_lookup [::33] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::33] 6 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1205_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_1205_sync.
 - exact ran.
Qed.
Lemma global_scalar_1205_step invalid snapshot final v initial
 (source_found:circuit_lookup [::33] 34 snapshot=Some(Gval (Fuint 1) (global_word_1204 v)))
 (initial_found:circuit_lookup [::33] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1204 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_1205 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 6 final=Some(Gval (Fuint 1) (global_word_1205 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=1) (ports:=multiplier_ports 1) (stmts:=generated_module_1_stmts_0) (source:=34).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1205_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_1205_sync.
 - exact ran.
Qed.
Lemma global_scalar_1219_syntax : framed_write_certificate 4
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 4) (@Eref VarOrder.T (@Eid VarOrder.T 25))) generated_module_0_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_1219_sync : node_sync_check generated_modules multiplier_instances [::34] 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_1219_type invalid snapshot final initial
 (initial_found:circuit_lookup [::34] 4 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::34] 4 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=25).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1219_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_1219_sync.
 - exact ran.
Qed.
Lemma global_scalar_1219_step invalid snapshot final v initial
 (source_found:circuit_lookup [::34] 25 snapshot=Some(Gval (Fuint 1) (global_word_1218 v)))
 (initial_found:circuit_lookup [::34] 4 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1218 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_1219 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::34] 4 final=Some(Gval (Fuint 1) (global_word_1219 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=25).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1219_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_1219_sync.
 - exact ran.
Qed.
Lemma global_scalar_1223_syntax : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 26))) generated_module_0_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_1223_sync : node_sync_check generated_modules multiplier_instances [::34] 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_1223_type invalid snapshot final initial
 (initial_found:circuit_lookup [::34] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::34] 5 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=26).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1223_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_1223_sync.
 - exact ran.
Qed.
Lemma global_scalar_1223_step invalid snapshot final v initial
 (source_found:circuit_lookup [::34] 26 snapshot=Some(Gval (Fuint 1) (global_word_1222 v)))
 (initial_found:circuit_lookup [::34] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1222 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_1223 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::34] 5 final=Some(Gval (Fuint 1) (global_word_1223 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=26).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1223_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_1223_sync.
 - exact ran.
Qed.
Lemma global_scalar_1237_syntax : framed_write_certificate 4
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 4) (@Eref VarOrder.T (@Eid VarOrder.T 25))) generated_module_0_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_1237_sync : node_sync_check generated_modules multiplier_instances [::35] 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_1237_type invalid snapshot final initial
 (initial_found:circuit_lookup [::35] 4 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::35] 4 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=25).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1237_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_1237_sync.
 - exact ran.
Qed.
Lemma global_scalar_1237_step invalid snapshot final v initial
 (source_found:circuit_lookup [::35] 25 snapshot=Some(Gval (Fuint 1) (global_word_1236 v)))
 (initial_found:circuit_lookup [::35] 4 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1236 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_1237 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::35] 4 final=Some(Gval (Fuint 1) (global_word_1237 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=25).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1237_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_1237_sync.
 - exact ran.
Qed.
Lemma global_scalar_1241_syntax : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 26))) generated_module_0_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_1241_sync : node_sync_check generated_modules multiplier_instances [::35] 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_1241_type invalid snapshot final initial
 (initial_found:circuit_lookup [::35] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::35] 5 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=26).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1241_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_1241_sync.
 - exact ran.
Qed.
Lemma global_scalar_1241_step invalid snapshot final v initial
 (source_found:circuit_lookup [::35] 26 snapshot=Some(Gval (Fuint 1) (global_word_1240 v)))
 (initial_found:circuit_lookup [::35] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1240 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_1241 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::35] 5 final=Some(Gval (Fuint 1) (global_word_1241 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=26).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1241_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_1241_sync.
 - exact ran.
Qed.
Lemma global_scalar_1255_syntax : framed_write_certificate 4
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 4) (@Eref VarOrder.T (@Eid VarOrder.T 25))) generated_module_0_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_1255_sync : node_sync_check generated_modules multiplier_instances [::36] 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_1255_type invalid snapshot final initial
 (initial_found:circuit_lookup [::36] 4 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::36] 4 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=25).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1255_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_1255_sync.
 - exact ran.
Qed.
Lemma global_scalar_1255_step invalid snapshot final v initial
 (source_found:circuit_lookup [::36] 25 snapshot=Some(Gval (Fuint 1) (global_word_1254 v)))
 (initial_found:circuit_lookup [::36] 4 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1254 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_1255 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::36] 4 final=Some(Gval (Fuint 1) (global_word_1255 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=25).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1255_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_1255_sync.
 - exact ran.
Qed.
Lemma global_scalar_1259_syntax : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 26))) generated_module_0_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_1259_sync : node_sync_check generated_modules multiplier_instances [::36] 5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_1259_type invalid snapshot final initial
 (initial_found:circuit_lookup [::36] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::36] 5 final=Some result /\ type_of_val result=Gtyp (Fuint 1).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=26).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1259_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_1259_sync.
 - exact ran.
Qed.
Lemma global_scalar_1259_step invalid snapshot final v initial
 (source_found:circuit_lookup [::36] 26 snapshot=Some(Gval (Fuint 1) (global_word_1258 v)))
 (initial_found:circuit_lookup [::36] 5 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 1))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 1) (global_word_1258 v)) (Gtyp (Fuint 1))=Some(Gval (Fuint 1) (global_word_1259 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::36] 5 final=Some(Gval (Fuint 1) (global_word_1259 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=0) (ports:=multiplier_ports 0) (stmts:=generated_module_0_stmts_0) (source:=26).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1259_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_1259_sync.
 - exact ran.
Qed.
Lemma global_scalar_1299_syntax : framed_write_certificate 6
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 6) (@Eref VarOrder.T (@Eid VarOrder.T 403))) generated_module_3_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_1299_sync : node_sync_check generated_modules multiplier_instances [::] 6 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_1299_type invalid snapshot final initial
 (initial_found:circuit_lookup [::] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 16))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup [::] 6 final=Some result /\ type_of_val result=Gtyp (Fuint 16).
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (source:=403).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1299_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_1299_sync.
 - exact ran.
Qed.
Lemma global_scalar_1299_step invalid snapshot final v initial
 (source_found:circuit_lookup [::] 403 snapshot=Some(Gval (Fuint 16) (global_word_1292 v)))
 (initial_found:circuit_lookup [::] 6 snapshot=Some initial)
 (typed:type_of_val initial=Gtyp (Fuint 16))
 (adapted:adapt_hvalue_as_type (Gval (Fuint 16) (global_word_1292 v)) (Gtyp (Fuint 16))=Some(Gval (Fuint 16) (global_word_1299 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 6 final=Some(Gval (Fuint 16) (global_word_1299 v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0) (source:=403).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_1299_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_1299_sync.
 - exact ran.
Qed.
