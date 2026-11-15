From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import HierarchyFacts PortFieldFacts CircuitPortTypes.
From SmallMultiplier Require Import Model GlobalStable GlobalInstances GlobalSyncFacts InstanceChecks.
Local Open Scope N_scope.
Lemma global_sync_279_link invalid snapshot final v
 (source_after:circuit_interface [::] 7 2 final=Some(Gval (Fuint 1) (global_word_278 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::7] 2 final=Some(Gval (Fuint 1) (global_word_279 v)).
Proof. rewrite global_sync_279. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=7) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_279_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::7] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=7) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_282_link invalid snapshot final v
 (source_after:circuit_interface [::] 7 3 final=Some(Gval (Fuint 1) (global_word_281 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::7] 3 final=Some(Gval (Fuint 1) (global_word_282 v)).
Proof. rewrite global_sync_282. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=7) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_282_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::7] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=7) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_290_link invalid snapshot final v
 (source_after:circuit_lookup [::7] 4 final=Some(Gval (Fuint 1) (global_word_289 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 7 4 final=Some(Gval (Fuint 1) (global_word_290 v)).
Proof. rewrite global_sync_290. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=7) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_290_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 7 4 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=7) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_294_link invalid snapshot final v
 (source_after:circuit_lookup [::7] 5 final=Some(Gval (Fuint 1) (global_word_293 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 7 5 final=Some(Gval (Fuint 1) (global_word_294 v)).
Proof. rewrite global_sync_294. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=7) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_294_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 7 5 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=7) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_297_link invalid snapshot final v
 (source_after:circuit_interface [::] 8 2 final=Some(Gval (Fuint 1) (global_word_296 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::8] 2 final=Some(Gval (Fuint 1) (global_word_297 v)).
Proof. rewrite global_sync_297. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=8) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_297_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::8] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=8) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_300_link invalid snapshot final v
 (source_after:circuit_interface [::] 8 3 final=Some(Gval (Fuint 1) (global_word_299 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::8] 3 final=Some(Gval (Fuint 1) (global_word_300 v)).
Proof. rewrite global_sync_300. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=8) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_300_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::8] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=8) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_308_link invalid snapshot final v
 (source_after:circuit_lookup [::8] 4 final=Some(Gval (Fuint 1) (global_word_307 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 8 4 final=Some(Gval (Fuint 1) (global_word_308 v)).
Proof. rewrite global_sync_308. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=8) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_308_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 8 4 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=8) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_312_link invalid snapshot final v
 (source_after:circuit_lookup [::8] 5 final=Some(Gval (Fuint 1) (global_word_311 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 8 5 final=Some(Gval (Fuint 1) (global_word_312 v)).
Proof. rewrite global_sync_312. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=8) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_312_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 8 5 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=8) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_315_link invalid snapshot final v
 (source_after:circuit_interface [::] 9 4 final=Some(Gval (Fuint 1) (global_word_314 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::9] 4 final=Some(Gval (Fuint 1) (global_word_315 v)).
Proof. rewrite global_sync_315. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=9) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_315_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::9] 4 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=9) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_318_link invalid snapshot final v
 (source_after:circuit_interface [::] 9 2 final=Some(Gval (Fuint 1) (global_word_317 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::9] 2 final=Some(Gval (Fuint 1) (global_word_318 v)).
Proof. rewrite global_sync_318. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=9) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_318_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::9] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=9) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_321_link invalid snapshot final v
 (source_after:circuit_interface [::] 9 3 final=Some(Gval (Fuint 1) (global_word_320 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::9] 3 final=Some(Gval (Fuint 1) (global_word_321 v)).
Proof. rewrite global_sync_321. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=9) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_321_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::9] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=9) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_332_link invalid snapshot final v
 (source_after:circuit_lookup [::9] 5 final=Some(Gval (Fuint 1) (global_word_331 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 9 5 final=Some(Gval (Fuint 1) (global_word_332 v)).
Proof. rewrite global_sync_332. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=9) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_332_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 9 5 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=9) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_336_link invalid snapshot final v
 (source_after:circuit_lookup [::9] 6 final=Some(Gval (Fuint 1) (global_word_335 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 9 6 final=Some(Gval (Fuint 1) (global_word_336 v)).
Proof. rewrite global_sync_336. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=9) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_336_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 9 6 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=9) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_339_link invalid snapshot final v
 (source_after:circuit_interface [::] 10 4 final=Some(Gval (Fuint 1) (global_word_338 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10] 4 final=Some(Gval (Fuint 1) (global_word_339 v)).
Proof. rewrite global_sync_339. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_339_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10] 4 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_342_link invalid snapshot final v
 (source_after:circuit_interface [::] 10 2 final=Some(Gval (Fuint 1) (global_word_341 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10] 2 final=Some(Gval (Fuint 1) (global_word_342 v)).
Proof. rewrite global_sync_342. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_342_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_345_link invalid snapshot final v
 (source_after:circuit_interface [::] 10 3 final=Some(Gval (Fuint 1) (global_word_344 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10] 3 final=Some(Gval (Fuint 1) (global_word_345 v)).
Proof. rewrite global_sync_345. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_345_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_356_link invalid snapshot final v
 (source_after:circuit_lookup [::10] 5 final=Some(Gval (Fuint 1) (global_word_355 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 10 5 final=Some(Gval (Fuint 1) (global_word_356 v)).
Proof. rewrite global_sync_356. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_356_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 10 5 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_360_link invalid snapshot final v
 (source_after:circuit_lookup [::10] 6 final=Some(Gval (Fuint 1) (global_word_359 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 10 6 final=Some(Gval (Fuint 1) (global_word_360 v)).
Proof. rewrite global_sync_360. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_360_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 10 6 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_363_link invalid snapshot final v
 (source_after:circuit_interface [::] 11 6 final=Some(Gval (Fuint 1) (global_word_362 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11] 6 final=Some(Gval (Fuint 1) (global_word_363 v)).
Proof. rewrite global_sync_363. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_363_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11] 6 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_366_link invalid snapshot final v
 (source_after:circuit_interface [::11] 11 4 final=Some(Gval (Fuint 1) (global_word_365 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;11] 4 final=Some(Gval (Fuint 1) (global_word_366 v)).
Proof. rewrite global_sync_366. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::11]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_366_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;11] 4 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::11]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_369_link invalid snapshot final v
 (source_after:circuit_interface [::] 11 4 final=Some(Gval (Fuint 1) (global_word_368 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11] 4 final=Some(Gval (Fuint 1) (global_word_369 v)).
Proof. rewrite global_sync_369. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_369_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11] 4 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_371_link invalid snapshot final v
 (source_after:circuit_interface [::11] 10 4 final=Some(Gval (Fuint 1) (global_word_370 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;11] 4 final=Some(Gval (Fuint 1) (global_word_371 v)).
Proof. rewrite global_sync_371. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::11]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_371_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;11] 4 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::11]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_374_link invalid snapshot final v
 (source_after:circuit_interface [::] 11 2 final=Some(Gval (Fuint 1) (global_word_373 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11] 2 final=Some(Gval (Fuint 1) (global_word_374 v)).
Proof. rewrite global_sync_374. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_374_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_376_link invalid snapshot final v
 (source_after:circuit_interface [::11] 10 2 final=Some(Gval (Fuint 1) (global_word_375 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;11] 2 final=Some(Gval (Fuint 1) (global_word_376 v)).
Proof. rewrite global_sync_376. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::11]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_376_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;11] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::11]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_379_link invalid snapshot final v
 (source_after:circuit_interface [::] 11 3 final=Some(Gval (Fuint 1) (global_word_378 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11] 3 final=Some(Gval (Fuint 1) (global_word_379 v)).
Proof. rewrite global_sync_379. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_379_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_381_link invalid snapshot final v
 (source_after:circuit_interface [::11] 10 3 final=Some(Gval (Fuint 1) (global_word_380 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;11] 3 final=Some(Gval (Fuint 1) (global_word_381 v)).
Proof. rewrite global_sync_381. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::11]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_381_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;11] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::11]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_392_link invalid snapshot final v
 (source_after:circuit_lookup [::10;11] 5 final=Some(Gval (Fuint 1) (global_word_391 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::11] 10 5 final=Some(Gval (Fuint 1) (global_word_392 v)).
Proof. rewrite global_sync_392. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::11]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_392_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::11] 10 5 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::11]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_395_link invalid snapshot final v
 (source_after:circuit_interface [::11] 11 2 final=Some(Gval (Fuint 1) (global_word_394 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;11] 2 final=Some(Gval (Fuint 1) (global_word_395 v)).
Proof. rewrite global_sync_395. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::11]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_395_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;11] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::11]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_398_link invalid snapshot final v
 (source_after:circuit_interface [::] 11 5 final=Some(Gval (Fuint 1) (global_word_397 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11] 5 final=Some(Gval (Fuint 1) (global_word_398 v)).
Proof. rewrite global_sync_398. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_398_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11] 5 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_401_link invalid snapshot final v
 (source_after:circuit_interface [::11] 11 3 final=Some(Gval (Fuint 1) (global_word_400 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;11] 3 final=Some(Gval (Fuint 1) (global_word_401 v)).
Proof. rewrite global_sync_401. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::11]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_401_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;11] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::11]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_412_link invalid snapshot final v
 (source_after:circuit_lookup [::11;11] 5 final=Some(Gval (Fuint 1) (global_word_411 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::11] 11 5 final=Some(Gval (Fuint 1) (global_word_412 v)).
Proof. rewrite global_sync_412. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::11]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_412_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::11] 11 5 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::11]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_415_link invalid snapshot final v
 (source_after:circuit_lookup [::11] 7 final=Some(Gval (Fuint 1) (global_word_414 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 11 7 final=Some(Gval (Fuint 1) (global_word_415 v)).
Proof. rewrite global_sync_415. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_415_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 11 7 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_419_link invalid snapshot final v
 (source_after:circuit_lookup [::10;11] 6 final=Some(Gval (Fuint 1) (global_word_418 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::11] 10 6 final=Some(Gval (Fuint 1) (global_word_419 v)).
Proof. rewrite global_sync_419. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::11]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_419_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::11] 10 6 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::11]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_422_link invalid snapshot final v
 (source_after:circuit_lookup [::11] 8 final=Some(Gval (Fuint 1) (global_word_421 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 11 8 final=Some(Gval (Fuint 1) (global_word_422 v)).
Proof. rewrite global_sync_422. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_422_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 11 8 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_426_link invalid snapshot final v
 (source_after:circuit_lookup [::11;11] 6 final=Some(Gval (Fuint 1) (global_word_425 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::11] 11 6 final=Some(Gval (Fuint 1) (global_word_426 v)).
Proof. rewrite global_sync_426. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::11]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_426_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::11] 11 6 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::11]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_429_link invalid snapshot final v
 (source_after:circuit_lookup [::11] 9 final=Some(Gval (Fuint 1) (global_word_428 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 11 9 final=Some(Gval (Fuint 1) (global_word_429 v)).
Proof. rewrite global_sync_429. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_429_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 11 9 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_432_link invalid snapshot final v
 (source_after:circuit_interface [::] 12 6 final=Some(Gval (Fuint 1) (global_word_431 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::12] 6 final=Some(Gval (Fuint 1) (global_word_432 v)).
Proof. rewrite global_sync_432. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=12) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_432_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::12] 6 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=12) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_435_link invalid snapshot final v
 (source_after:circuit_interface [::12] 11 4 final=Some(Gval (Fuint 1) (global_word_434 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;12] 4 final=Some(Gval (Fuint 1) (global_word_435 v)).
Proof. rewrite global_sync_435. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::12]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_435_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;12] 4 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::12]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_438_link invalid snapshot final v
 (source_after:circuit_interface [::] 12 4 final=Some(Gval (Fuint 1) (global_word_437 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::12] 4 final=Some(Gval (Fuint 1) (global_word_438 v)).
Proof. rewrite global_sync_438. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=12) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_438_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::12] 4 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=12) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_440_link invalid snapshot final v
 (source_after:circuit_interface [::12] 10 4 final=Some(Gval (Fuint 1) (global_word_439 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;12] 4 final=Some(Gval (Fuint 1) (global_word_440 v)).
Proof. rewrite global_sync_440. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::12]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_440_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;12] 4 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::12]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_443_link invalid snapshot final v
 (source_after:circuit_interface [::] 12 2 final=Some(Gval (Fuint 1) (global_word_442 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::12] 2 final=Some(Gval (Fuint 1) (global_word_443 v)).
Proof. rewrite global_sync_443. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=12) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_443_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::12] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=12) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_445_link invalid snapshot final v
 (source_after:circuit_interface [::12] 10 2 final=Some(Gval (Fuint 1) (global_word_444 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;12] 2 final=Some(Gval (Fuint 1) (global_word_445 v)).
Proof. rewrite global_sync_445. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::12]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_445_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;12] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::12]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_448_link invalid snapshot final v
 (source_after:circuit_interface [::] 12 3 final=Some(Gval (Fuint 1) (global_word_447 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::12] 3 final=Some(Gval (Fuint 1) (global_word_448 v)).
Proof. rewrite global_sync_448. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=12) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_448_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::12] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=12) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_450_link invalid snapshot final v
 (source_after:circuit_interface [::12] 10 3 final=Some(Gval (Fuint 1) (global_word_449 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;12] 3 final=Some(Gval (Fuint 1) (global_word_450 v)).
Proof. rewrite global_sync_450. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::12]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_450_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;12] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::12]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_461_link invalid snapshot final v
 (source_after:circuit_lookup [::10;12] 5 final=Some(Gval (Fuint 1) (global_word_460 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::12] 10 5 final=Some(Gval (Fuint 1) (global_word_461 v)).
Proof. rewrite global_sync_461. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::12]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_461_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::12] 10 5 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::12]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_464_link invalid snapshot final v
 (source_after:circuit_interface [::12] 11 2 final=Some(Gval (Fuint 1) (global_word_463 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;12] 2 final=Some(Gval (Fuint 1) (global_word_464 v)).
Proof. rewrite global_sync_464. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::12]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_464_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;12] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::12]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_467_link invalid snapshot final v
 (source_after:circuit_interface [::] 12 5 final=Some(Gval (Fuint 1) (global_word_466 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::12] 5 final=Some(Gval (Fuint 1) (global_word_467 v)).
Proof. rewrite global_sync_467. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=12) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_467_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::12] 5 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=12) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_470_link invalid snapshot final v
 (source_after:circuit_interface [::12] 11 3 final=Some(Gval (Fuint 1) (global_word_469 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;12] 3 final=Some(Gval (Fuint 1) (global_word_470 v)).
Proof. rewrite global_sync_470. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::12]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_470_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;12] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::12]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_481_link invalid snapshot final v
 (source_after:circuit_lookup [::11;12] 5 final=Some(Gval (Fuint 1) (global_word_480 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::12] 11 5 final=Some(Gval (Fuint 1) (global_word_481 v)).
Proof. rewrite global_sync_481. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::12]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_481_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::12] 11 5 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::12]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_484_link invalid snapshot final v
 (source_after:circuit_lookup [::12] 7 final=Some(Gval (Fuint 1) (global_word_483 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 12 7 final=Some(Gval (Fuint 1) (global_word_484 v)).
Proof. rewrite global_sync_484. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=12) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_484_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 12 7 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=12) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_488_link invalid snapshot final v
 (source_after:circuit_lookup [::10;12] 6 final=Some(Gval (Fuint 1) (global_word_487 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::12] 10 6 final=Some(Gval (Fuint 1) (global_word_488 v)).
Proof. rewrite global_sync_488. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::12]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_488_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::12] 10 6 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::12]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_491_link invalid snapshot final v
 (source_after:circuit_lookup [::12] 8 final=Some(Gval (Fuint 1) (global_word_490 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 12 8 final=Some(Gval (Fuint 1) (global_word_491 v)).
Proof. rewrite global_sync_491. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=12) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_491_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 12 8 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=12) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_495_link invalid snapshot final v
 (source_after:circuit_lookup [::11;12] 6 final=Some(Gval (Fuint 1) (global_word_494 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::12] 11 6 final=Some(Gval (Fuint 1) (global_word_495 v)).
Proof. rewrite global_sync_495. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::12]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_495_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::12] 11 6 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::12]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_498_link invalid snapshot final v
 (source_after:circuit_lookup [::12] 9 final=Some(Gval (Fuint 1) (global_word_497 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 12 9 final=Some(Gval (Fuint 1) (global_word_498 v)).
Proof. rewrite global_sync_498. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=12) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_498_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 12 9 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=12) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_501_link invalid snapshot final v
 (source_after:circuit_interface [::] 13 6 final=Some(Gval (Fuint 1) (global_word_500 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::13] 6 final=Some(Gval (Fuint 1) (global_word_501 v)).
Proof. rewrite global_sync_501. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=13) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_501_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::13] 6 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=13) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_504_link invalid snapshot final v
 (source_after:circuit_interface [::13] 11 4 final=Some(Gval (Fuint 1) (global_word_503 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;13] 4 final=Some(Gval (Fuint 1) (global_word_504 v)).
Proof. rewrite global_sync_504. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::13]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_504_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;13] 4 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::13]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_507_link invalid snapshot final v
 (source_after:circuit_interface [::] 13 4 final=Some(Gval (Fuint 1) (global_word_506 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::13] 4 final=Some(Gval (Fuint 1) (global_word_507 v)).
Proof. rewrite global_sync_507. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=13) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_507_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::13] 4 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=13) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_509_link invalid snapshot final v
 (source_after:circuit_interface [::13] 10 4 final=Some(Gval (Fuint 1) (global_word_508 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;13] 4 final=Some(Gval (Fuint 1) (global_word_509 v)).
Proof. rewrite global_sync_509. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::13]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_509_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;13] 4 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::13]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_512_link invalid snapshot final v
 (source_after:circuit_interface [::] 13 2 final=Some(Gval (Fuint 1) (global_word_511 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::13] 2 final=Some(Gval (Fuint 1) (global_word_512 v)).
Proof. rewrite global_sync_512. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=13) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_512_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::13] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=13) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_514_link invalid snapshot final v
 (source_after:circuit_interface [::13] 10 2 final=Some(Gval (Fuint 1) (global_word_513 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;13] 2 final=Some(Gval (Fuint 1) (global_word_514 v)).
Proof. rewrite global_sync_514. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::13]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_514_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;13] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::13]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_517_link invalid snapshot final v
 (source_after:circuit_interface [::] 13 3 final=Some(Gval (Fuint 1) (global_word_516 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::13] 3 final=Some(Gval (Fuint 1) (global_word_517 v)).
Proof. rewrite global_sync_517. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=13) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_517_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::13] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=13) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_519_link invalid snapshot final v
 (source_after:circuit_interface [::13] 10 3 final=Some(Gval (Fuint 1) (global_word_518 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;13] 3 final=Some(Gval (Fuint 1) (global_word_519 v)).
Proof. rewrite global_sync_519. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::13]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_519_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;13] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::13]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_530_link invalid snapshot final v
 (source_after:circuit_lookup [::10;13] 5 final=Some(Gval (Fuint 1) (global_word_529 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::13] 10 5 final=Some(Gval (Fuint 1) (global_word_530 v)).
Proof. rewrite global_sync_530. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::13]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_530_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::13] 10 5 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::13]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_533_link invalid snapshot final v
 (source_after:circuit_interface [::13] 11 2 final=Some(Gval (Fuint 1) (global_word_532 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;13] 2 final=Some(Gval (Fuint 1) (global_word_533 v)).
Proof. rewrite global_sync_533. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::13]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_533_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;13] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::13]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_536_link invalid snapshot final v
 (source_after:circuit_interface [::] 13 5 final=Some(Gval (Fuint 1) (global_word_535 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::13] 5 final=Some(Gval (Fuint 1) (global_word_536 v)).
Proof. rewrite global_sync_536. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=13) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_536_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::13] 5 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=13) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_539_link invalid snapshot final v
 (source_after:circuit_interface [::13] 11 3 final=Some(Gval (Fuint 1) (global_word_538 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;13] 3 final=Some(Gval (Fuint 1) (global_word_539 v)).
Proof. rewrite global_sync_539. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::13]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_539_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;13] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::13]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_550_link invalid snapshot final v
 (source_after:circuit_lookup [::11;13] 5 final=Some(Gval (Fuint 1) (global_word_549 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::13] 11 5 final=Some(Gval (Fuint 1) (global_word_550 v)).
Proof. rewrite global_sync_550. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::13]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_550_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::13] 11 5 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::13]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_553_link invalid snapshot final v
 (source_after:circuit_lookup [::13] 7 final=Some(Gval (Fuint 1) (global_word_552 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 13 7 final=Some(Gval (Fuint 1) (global_word_553 v)).
Proof. rewrite global_sync_553. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=13) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_553_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 13 7 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=13) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_557_link invalid snapshot final v
 (source_after:circuit_lookup [::10;13] 6 final=Some(Gval (Fuint 1) (global_word_556 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::13] 10 6 final=Some(Gval (Fuint 1) (global_word_557 v)).
Proof. rewrite global_sync_557. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::13]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_557_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::13] 10 6 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::13]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_560_link invalid snapshot final v
 (source_after:circuit_lookup [::13] 8 final=Some(Gval (Fuint 1) (global_word_559 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 13 8 final=Some(Gval (Fuint 1) (global_word_560 v)).
Proof. rewrite global_sync_560. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=13) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_560_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 13 8 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=13) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_564_link invalid snapshot final v
 (source_after:circuit_lookup [::11;13] 6 final=Some(Gval (Fuint 1) (global_word_563 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::13] 11 6 final=Some(Gval (Fuint 1) (global_word_564 v)).
Proof. rewrite global_sync_564. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::13]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_564_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::13] 11 6 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::13]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_567_link invalid snapshot final v
 (source_after:circuit_lookup [::13] 9 final=Some(Gval (Fuint 1) (global_word_566 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 13 9 final=Some(Gval (Fuint 1) (global_word_567 v)).
Proof. rewrite global_sync_567. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=13) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_567_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 13 9 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=13) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_570_link invalid snapshot final v
 (source_after:circuit_interface [::] 14 6 final=Some(Gval (Fuint 1) (global_word_569 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::14] 6 final=Some(Gval (Fuint 1) (global_word_570 v)).
Proof. rewrite global_sync_570. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=14) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_570_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::14] 6 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=14) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_573_link invalid snapshot final v
 (source_after:circuit_interface [::14] 11 4 final=Some(Gval (Fuint 1) (global_word_572 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;14] 4 final=Some(Gval (Fuint 1) (global_word_573 v)).
Proof. rewrite global_sync_573. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::14]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_573_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;14] 4 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::14]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_576_link invalid snapshot final v
 (source_after:circuit_interface [::] 14 4 final=Some(Gval (Fuint 1) (global_word_575 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::14] 4 final=Some(Gval (Fuint 1) (global_word_576 v)).
Proof. rewrite global_sync_576. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=14) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_576_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::14] 4 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=14) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_578_link invalid snapshot final v
 (source_after:circuit_interface [::14] 10 4 final=Some(Gval (Fuint 1) (global_word_577 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;14] 4 final=Some(Gval (Fuint 1) (global_word_578 v)).
Proof. rewrite global_sync_578. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::14]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_578_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;14] 4 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::14]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_581_link invalid snapshot final v
 (source_after:circuit_interface [::] 14 2 final=Some(Gval (Fuint 1) (global_word_580 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::14] 2 final=Some(Gval (Fuint 1) (global_word_581 v)).
Proof. rewrite global_sync_581. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=14) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_581_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::14] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=14) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_583_link invalid snapshot final v
 (source_after:circuit_interface [::14] 10 2 final=Some(Gval (Fuint 1) (global_word_582 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;14] 2 final=Some(Gval (Fuint 1) (global_word_583 v)).
Proof. rewrite global_sync_583. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::14]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_583_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;14] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::14]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_586_link invalid snapshot final v
 (source_after:circuit_interface [::] 14 3 final=Some(Gval (Fuint 1) (global_word_585 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::14] 3 final=Some(Gval (Fuint 1) (global_word_586 v)).
Proof. rewrite global_sync_586. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=14) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_586_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::14] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=14) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_588_link invalid snapshot final v
 (source_after:circuit_interface [::14] 10 3 final=Some(Gval (Fuint 1) (global_word_587 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;14] 3 final=Some(Gval (Fuint 1) (global_word_588 v)).
Proof. rewrite global_sync_588. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::14]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_588_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;14] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::14]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_599_link invalid snapshot final v
 (source_after:circuit_lookup [::10;14] 5 final=Some(Gval (Fuint 1) (global_word_598 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::14] 10 5 final=Some(Gval (Fuint 1) (global_word_599 v)).
Proof. rewrite global_sync_599. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::14]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_599_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::14] 10 5 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::14]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_602_link invalid snapshot final v
 (source_after:circuit_interface [::14] 11 2 final=Some(Gval (Fuint 1) (global_word_601 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;14] 2 final=Some(Gval (Fuint 1) (global_word_602 v)).
Proof. rewrite global_sync_602. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::14]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_602_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;14] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::14]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_605_link invalid snapshot final v
 (source_after:circuit_interface [::] 14 5 final=Some(Gval (Fuint 1) (global_word_604 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::14] 5 final=Some(Gval (Fuint 1) (global_word_605 v)).
Proof. rewrite global_sync_605. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=14) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_605_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::14] 5 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=14) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_608_link invalid snapshot final v
 (source_after:circuit_interface [::14] 11 3 final=Some(Gval (Fuint 1) (global_word_607 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;14] 3 final=Some(Gval (Fuint 1) (global_word_608 v)).
Proof. rewrite global_sync_608. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::14]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_608_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;14] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::14]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_619_link invalid snapshot final v
 (source_after:circuit_lookup [::11;14] 5 final=Some(Gval (Fuint 1) (global_word_618 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::14] 11 5 final=Some(Gval (Fuint 1) (global_word_619 v)).
Proof. rewrite global_sync_619. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::14]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_619_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::14] 11 5 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::14]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_622_link invalid snapshot final v
 (source_after:circuit_lookup [::14] 7 final=Some(Gval (Fuint 1) (global_word_621 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 14 7 final=Some(Gval (Fuint 1) (global_word_622 v)).
Proof. rewrite global_sync_622. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=14) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_622_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 14 7 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=14) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_626_link invalid snapshot final v
 (source_after:circuit_lookup [::10;14] 6 final=Some(Gval (Fuint 1) (global_word_625 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::14] 10 6 final=Some(Gval (Fuint 1) (global_word_626 v)).
Proof. rewrite global_sync_626. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::14]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_626_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::14] 10 6 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::14]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_629_link invalid snapshot final v
 (source_after:circuit_lookup [::14] 8 final=Some(Gval (Fuint 1) (global_word_628 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 14 8 final=Some(Gval (Fuint 1) (global_word_629 v)).
Proof. rewrite global_sync_629. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=14) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_629_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 14 8 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=14) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_633_link invalid snapshot final v
 (source_after:circuit_lookup [::11;14] 6 final=Some(Gval (Fuint 1) (global_word_632 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::14] 11 6 final=Some(Gval (Fuint 1) (global_word_633 v)).
Proof. rewrite global_sync_633. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::14]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_633_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::14] 11 6 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::14]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_636_link invalid snapshot final v
 (source_after:circuit_lookup [::14] 9 final=Some(Gval (Fuint 1) (global_word_635 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 14 9 final=Some(Gval (Fuint 1) (global_word_636 v)).
Proof. rewrite global_sync_636. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=14) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_636_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 14 9 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=14) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_639_link invalid snapshot final v
 (source_after:circuit_interface [::] 15 6 final=Some(Gval (Fuint 1) (global_word_638 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::15] 6 final=Some(Gval (Fuint 1) (global_word_639 v)).
Proof. rewrite global_sync_639. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=15) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_639_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::15] 6 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=15) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_642_link invalid snapshot final v
 (source_after:circuit_interface [::15] 11 4 final=Some(Gval (Fuint 1) (global_word_641 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;15] 4 final=Some(Gval (Fuint 1) (global_word_642 v)).
Proof. rewrite global_sync_642. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::15]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_642_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;15] 4 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::15]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_645_link invalid snapshot final v
 (source_after:circuit_interface [::] 15 4 final=Some(Gval (Fuint 1) (global_word_644 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::15] 4 final=Some(Gval (Fuint 1) (global_word_645 v)).
Proof. rewrite global_sync_645. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=15) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_645_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::15] 4 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=15) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_647_link invalid snapshot final v
 (source_after:circuit_interface [::15] 10 4 final=Some(Gval (Fuint 1) (global_word_646 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;15] 4 final=Some(Gval (Fuint 1) (global_word_647 v)).
Proof. rewrite global_sync_647. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::15]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_647_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;15] 4 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::15]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_650_link invalid snapshot final v
 (source_after:circuit_interface [::] 15 2 final=Some(Gval (Fuint 1) (global_word_649 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::15] 2 final=Some(Gval (Fuint 1) (global_word_650 v)).
Proof. rewrite global_sync_650. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=15) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_650_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::15] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=15) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_652_link invalid snapshot final v
 (source_after:circuit_interface [::15] 10 2 final=Some(Gval (Fuint 1) (global_word_651 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;15] 2 final=Some(Gval (Fuint 1) (global_word_652 v)).
Proof. rewrite global_sync_652. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::15]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_652_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;15] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::15]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_655_link invalid snapshot final v
 (source_after:circuit_interface [::] 15 3 final=Some(Gval (Fuint 1) (global_word_654 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::15] 3 final=Some(Gval (Fuint 1) (global_word_655 v)).
Proof. rewrite global_sync_655. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=15) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_655_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::15] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=15) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_657_link invalid snapshot final v
 (source_after:circuit_interface [::15] 10 3 final=Some(Gval (Fuint 1) (global_word_656 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;15] 3 final=Some(Gval (Fuint 1) (global_word_657 v)).
Proof. rewrite global_sync_657. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::15]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_657_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;15] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::15]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_668_link invalid snapshot final v
 (source_after:circuit_lookup [::10;15] 5 final=Some(Gval (Fuint 1) (global_word_667 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::15] 10 5 final=Some(Gval (Fuint 1) (global_word_668 v)).
Proof. rewrite global_sync_668. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::15]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_668_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::15] 10 5 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::15]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_671_link invalid snapshot final v
 (source_after:circuit_interface [::15] 11 2 final=Some(Gval (Fuint 1) (global_word_670 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;15] 2 final=Some(Gval (Fuint 1) (global_word_671 v)).
Proof. rewrite global_sync_671. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::15]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_671_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;15] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::15]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_674_link invalid snapshot final v
 (source_after:circuit_interface [::] 15 5 final=Some(Gval (Fuint 1) (global_word_673 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::15] 5 final=Some(Gval (Fuint 1) (global_word_674 v)).
Proof. rewrite global_sync_674. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=15) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_674_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::15] 5 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=15) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_677_link invalid snapshot final v
 (source_after:circuit_interface [::15] 11 3 final=Some(Gval (Fuint 1) (global_word_676 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;15] 3 final=Some(Gval (Fuint 1) (global_word_677 v)).
Proof. rewrite global_sync_677. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::15]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_677_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;15] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::15]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_688_link invalid snapshot final v
 (source_after:circuit_lookup [::11;15] 5 final=Some(Gval (Fuint 1) (global_word_687 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::15] 11 5 final=Some(Gval (Fuint 1) (global_word_688 v)).
Proof. rewrite global_sync_688. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::15]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_688_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::15] 11 5 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::15]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_691_link invalid snapshot final v
 (source_after:circuit_lookup [::15] 7 final=Some(Gval (Fuint 1) (global_word_690 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 15 7 final=Some(Gval (Fuint 1) (global_word_691 v)).
Proof. rewrite global_sync_691. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=15) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_691_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 15 7 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=15) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_695_link invalid snapshot final v
 (source_after:circuit_lookup [::10;15] 6 final=Some(Gval (Fuint 1) (global_word_694 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::15] 10 6 final=Some(Gval (Fuint 1) (global_word_695 v)).
Proof. rewrite global_sync_695. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::15]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_695_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::15] 10 6 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::15]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_698_link invalid snapshot final v
 (source_after:circuit_lookup [::15] 8 final=Some(Gval (Fuint 1) (global_word_697 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 15 8 final=Some(Gval (Fuint 1) (global_word_698 v)).
Proof. rewrite global_sync_698. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=15) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_698_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 15 8 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=15) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_702_link invalid snapshot final v
 (source_after:circuit_lookup [::11;15] 6 final=Some(Gval (Fuint 1) (global_word_701 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::15] 11 6 final=Some(Gval (Fuint 1) (global_word_702 v)).
Proof. rewrite global_sync_702. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::15]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_702_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::15] 11 6 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::15]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_705_link invalid snapshot final v
 (source_after:circuit_lookup [::15] 9 final=Some(Gval (Fuint 1) (global_word_704 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 15 9 final=Some(Gval (Fuint 1) (global_word_705 v)).
Proof. rewrite global_sync_705. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=15) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_705_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 15 9 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=15) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_708_link invalid snapshot final v
 (source_after:circuit_interface [::] 16 6 final=Some(Gval (Fuint 1) (global_word_707 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::16] 6 final=Some(Gval (Fuint 1) (global_word_708 v)).
Proof. rewrite global_sync_708. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=16) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_708_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::16] 6 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=16) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_711_link invalid snapshot final v
 (source_after:circuit_interface [::16] 11 4 final=Some(Gval (Fuint 1) (global_word_710 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 4 final=Some(Gval (Fuint 1) (global_word_711 v)).
Proof. rewrite global_sync_711. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::16]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_711_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;16] 4 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::16]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_714_link invalid snapshot final v
 (source_after:circuit_interface [::] 16 4 final=Some(Gval (Fuint 1) (global_word_713 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::16] 4 final=Some(Gval (Fuint 1) (global_word_714 v)).
Proof. rewrite global_sync_714. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=16) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_714_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::16] 4 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=16) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_716_link invalid snapshot final v
 (source_after:circuit_interface [::16] 10 4 final=Some(Gval (Fuint 1) (global_word_715 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 4 final=Some(Gval (Fuint 1) (global_word_716 v)).
Proof. rewrite global_sync_716. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::16]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_716_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;16] 4 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::16]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_719_link invalid snapshot final v
 (source_after:circuit_interface [::] 16 2 final=Some(Gval (Fuint 1) (global_word_718 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::16] 2 final=Some(Gval (Fuint 1) (global_word_719 v)).
Proof. rewrite global_sync_719. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=16) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_719_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::16] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=16) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_721_link invalid snapshot final v
 (source_after:circuit_interface [::16] 10 2 final=Some(Gval (Fuint 1) (global_word_720 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 2 final=Some(Gval (Fuint 1) (global_word_721 v)).
Proof. rewrite global_sync_721. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::16]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_721_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;16] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::16]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_724_link invalid snapshot final v
 (source_after:circuit_interface [::] 16 3 final=Some(Gval (Fuint 1) (global_word_723 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::16] 3 final=Some(Gval (Fuint 1) (global_word_724 v)).
Proof. rewrite global_sync_724. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=16) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_724_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::16] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=16) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_726_link invalid snapshot final v
 (source_after:circuit_interface [::16] 10 3 final=Some(Gval (Fuint 1) (global_word_725 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 3 final=Some(Gval (Fuint 1) (global_word_726 v)).
Proof. rewrite global_sync_726. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::16]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_726_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;16] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::16]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_737_link invalid snapshot final v
 (source_after:circuit_lookup [::10;16] 5 final=Some(Gval (Fuint 1) (global_word_736 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::16] 10 5 final=Some(Gval (Fuint 1) (global_word_737 v)).
Proof. rewrite global_sync_737. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::16]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_737_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::16] 10 5 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::16]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_740_link invalid snapshot final v
 (source_after:circuit_interface [::16] 11 2 final=Some(Gval (Fuint 1) (global_word_739 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 2 final=Some(Gval (Fuint 1) (global_word_740 v)).
Proof. rewrite global_sync_740. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::16]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_740_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;16] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::16]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_743_link invalid snapshot final v
 (source_after:circuit_interface [::] 16 5 final=Some(Gval (Fuint 1) (global_word_742 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::16] 5 final=Some(Gval (Fuint 1) (global_word_743 v)).
Proof. rewrite global_sync_743. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=16) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_743_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::16] 5 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=16) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_746_link invalid snapshot final v
 (source_after:circuit_interface [::16] 11 3 final=Some(Gval (Fuint 1) (global_word_745 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 3 final=Some(Gval (Fuint 1) (global_word_746 v)).
Proof. rewrite global_sync_746. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::16]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_746_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;16] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::16]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_757_link invalid snapshot final v
 (source_after:circuit_lookup [::11;16] 5 final=Some(Gval (Fuint 1) (global_word_756 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::16] 11 5 final=Some(Gval (Fuint 1) (global_word_757 v)).
Proof. rewrite global_sync_757. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::16]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_757_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::16] 11 5 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::16]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_760_link invalid snapshot final v
 (source_after:circuit_lookup [::16] 7 final=Some(Gval (Fuint 1) (global_word_759 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 16 7 final=Some(Gval (Fuint 1) (global_word_760 v)).
Proof. rewrite global_sync_760. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=16) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_760_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 16 7 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=16) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_764_link invalid snapshot final v
 (source_after:circuit_lookup [::10;16] 6 final=Some(Gval (Fuint 1) (global_word_763 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::16] 10 6 final=Some(Gval (Fuint 1) (global_word_764 v)).
Proof. rewrite global_sync_764. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::16]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_764_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::16] 10 6 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::16]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_767_link invalid snapshot final v
 (source_after:circuit_lookup [::16] 8 final=Some(Gval (Fuint 1) (global_word_766 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 16 8 final=Some(Gval (Fuint 1) (global_word_767 v)).
Proof. rewrite global_sync_767. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=16) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_767_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 16 8 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=16) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_771_link invalid snapshot final v
 (source_after:circuit_lookup [::11;16] 6 final=Some(Gval (Fuint 1) (global_word_770 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::16] 11 6 final=Some(Gval (Fuint 1) (global_word_771 v)).
Proof. rewrite global_sync_771. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::16]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_771_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::16] 11 6 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::16]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_774_link invalid snapshot final v
 (source_after:circuit_lookup [::16] 9 final=Some(Gval (Fuint 1) (global_word_773 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 16 9 final=Some(Gval (Fuint 1) (global_word_774 v)).
Proof. rewrite global_sync_774. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=16) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_774_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 16 9 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=16) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_777_link invalid snapshot final v
 (source_after:circuit_interface [::] 17 6 final=Some(Gval (Fuint 1) (global_word_776 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 6 final=Some(Gval (Fuint 1) (global_word_777 v)).
Proof. rewrite global_sync_777. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=17) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_777_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::17] 6 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=17) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_780_link invalid snapshot final v
 (source_after:circuit_interface [::17] 11 4 final=Some(Gval (Fuint 1) (global_word_779 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 4 final=Some(Gval (Fuint 1) (global_word_780 v)).
Proof. rewrite global_sync_780. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::17]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_780_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;17] 4 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::17]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_783_link invalid snapshot final v
 (source_after:circuit_interface [::] 17 4 final=Some(Gval (Fuint 1) (global_word_782 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 4 final=Some(Gval (Fuint 1) (global_word_783 v)).
Proof. rewrite global_sync_783. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=17) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_783_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::17] 4 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=17) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_785_link invalid snapshot final v
 (source_after:circuit_interface [::17] 10 4 final=Some(Gval (Fuint 1) (global_word_784 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 4 final=Some(Gval (Fuint 1) (global_word_785 v)).
Proof. rewrite global_sync_785. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::17]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_785_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;17] 4 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::17]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_788_link invalid snapshot final v
 (source_after:circuit_interface [::] 17 2 final=Some(Gval (Fuint 1) (global_word_787 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 2 final=Some(Gval (Fuint 1) (global_word_788 v)).
Proof. rewrite global_sync_788. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=17) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_788_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::17] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=17) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_790_link invalid snapshot final v
 (source_after:circuit_interface [::17] 10 2 final=Some(Gval (Fuint 1) (global_word_789 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 2 final=Some(Gval (Fuint 1) (global_word_790 v)).
Proof. rewrite global_sync_790. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::17]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_790_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;17] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::17]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_793_link invalid snapshot final v
 (source_after:circuit_interface [::] 17 3 final=Some(Gval (Fuint 1) (global_word_792 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 3 final=Some(Gval (Fuint 1) (global_word_793 v)).
Proof. rewrite global_sync_793. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=17) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_793_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::17] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=17) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_795_link invalid snapshot final v
 (source_after:circuit_interface [::17] 10 3 final=Some(Gval (Fuint 1) (global_word_794 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 3 final=Some(Gval (Fuint 1) (global_word_795 v)).
Proof. rewrite global_sync_795. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::17]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_795_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;17] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::17]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_806_link invalid snapshot final v
 (source_after:circuit_lookup [::10;17] 5 final=Some(Gval (Fuint 1) (global_word_805 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::17] 10 5 final=Some(Gval (Fuint 1) (global_word_806 v)).
Proof. rewrite global_sync_806. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::17]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_806_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::17] 10 5 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::17]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_809_link invalid snapshot final v
 (source_after:circuit_interface [::17] 11 2 final=Some(Gval (Fuint 1) (global_word_808 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 2 final=Some(Gval (Fuint 1) (global_word_809 v)).
Proof. rewrite global_sync_809. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::17]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_809_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;17] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::17]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_812_link invalid snapshot final v
 (source_after:circuit_interface [::] 17 5 final=Some(Gval (Fuint 1) (global_word_811 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 5 final=Some(Gval (Fuint 1) (global_word_812 v)).
Proof. rewrite global_sync_812. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=17) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_812_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::17] 5 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=17) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_815_link invalid snapshot final v
 (source_after:circuit_interface [::17] 11 3 final=Some(Gval (Fuint 1) (global_word_814 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 3 final=Some(Gval (Fuint 1) (global_word_815 v)).
Proof. rewrite global_sync_815. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::17]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_815_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;17] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::17]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_826_link invalid snapshot final v
 (source_after:circuit_lookup [::11;17] 5 final=Some(Gval (Fuint 1) (global_word_825 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::17] 11 5 final=Some(Gval (Fuint 1) (global_word_826 v)).
Proof. rewrite global_sync_826. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::17]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_826_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::17] 11 5 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::17]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_829_link invalid snapshot final v
 (source_after:circuit_lookup [::17] 7 final=Some(Gval (Fuint 1) (global_word_828 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 17 7 final=Some(Gval (Fuint 1) (global_word_829 v)).
Proof. rewrite global_sync_829. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=17) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_829_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 17 7 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=17) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_833_link invalid snapshot final v
 (source_after:circuit_lookup [::10;17] 6 final=Some(Gval (Fuint 1) (global_word_832 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::17] 10 6 final=Some(Gval (Fuint 1) (global_word_833 v)).
Proof. rewrite global_sync_833. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::17]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_833_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::17] 10 6 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::17]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_836_link invalid snapshot final v
 (source_after:circuit_lookup [::17] 8 final=Some(Gval (Fuint 1) (global_word_835 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 17 8 final=Some(Gval (Fuint 1) (global_word_836 v)).
Proof. rewrite global_sync_836. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=17) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_836_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 17 8 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=17) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_840_link invalid snapshot final v
 (source_after:circuit_lookup [::11;17] 6 final=Some(Gval (Fuint 1) (global_word_839 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::17] 11 6 final=Some(Gval (Fuint 1) (global_word_840 v)).
Proof. rewrite global_sync_840. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::17]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_840_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::17] 11 6 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::17]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_843_link invalid snapshot final v
 (source_after:circuit_lookup [::17] 9 final=Some(Gval (Fuint 1) (global_word_842 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 17 9 final=Some(Gval (Fuint 1) (global_word_843 v)).
Proof. rewrite global_sync_843. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=17) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_843_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 17 9 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=17) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_846_link invalid snapshot final v
 (source_after:circuit_interface [::] 18 6 final=Some(Gval (Fuint 1) (global_word_845 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 6 final=Some(Gval (Fuint 1) (global_word_846 v)).
Proof. rewrite global_sync_846. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=18) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_846_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::18] 6 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=18) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_849_link invalid snapshot final v
 (source_after:circuit_interface [::18] 11 4 final=Some(Gval (Fuint 1) (global_word_848 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 4 final=Some(Gval (Fuint 1) (global_word_849 v)).
Proof. rewrite global_sync_849. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::18]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_849_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;18] 4 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::18]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_852_link invalid snapshot final v
 (source_after:circuit_interface [::] 18 4 final=Some(Gval (Fuint 1) (global_word_851 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 4 final=Some(Gval (Fuint 1) (global_word_852 v)).
Proof. rewrite global_sync_852. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=18) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_852_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::18] 4 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=18) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_854_link invalid snapshot final v
 (source_after:circuit_interface [::18] 10 4 final=Some(Gval (Fuint 1) (global_word_853 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 4 final=Some(Gval (Fuint 1) (global_word_854 v)).
Proof. rewrite global_sync_854. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::18]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_854_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;18] 4 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::18]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_857_link invalid snapshot final v
 (source_after:circuit_interface [::] 18 2 final=Some(Gval (Fuint 1) (global_word_856 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 2 final=Some(Gval (Fuint 1) (global_word_857 v)).
Proof. rewrite global_sync_857. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=18) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_857_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::18] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=18) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_859_link invalid snapshot final v
 (source_after:circuit_interface [::18] 10 2 final=Some(Gval (Fuint 1) (global_word_858 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 2 final=Some(Gval (Fuint 1) (global_word_859 v)).
Proof. rewrite global_sync_859. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::18]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_859_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;18] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::18]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_862_link invalid snapshot final v
 (source_after:circuit_interface [::] 18 3 final=Some(Gval (Fuint 1) (global_word_861 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 3 final=Some(Gval (Fuint 1) (global_word_862 v)).
Proof. rewrite global_sync_862. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=18) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_862_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::18] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=18) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_864_link invalid snapshot final v
 (source_after:circuit_interface [::18] 10 3 final=Some(Gval (Fuint 1) (global_word_863 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 3 final=Some(Gval (Fuint 1) (global_word_864 v)).
Proof. rewrite global_sync_864. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::18]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_864_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;18] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::18]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_875_link invalid snapshot final v
 (source_after:circuit_lookup [::10;18] 5 final=Some(Gval (Fuint 1) (global_word_874 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::18] 10 5 final=Some(Gval (Fuint 1) (global_word_875 v)).
Proof. rewrite global_sync_875. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::18]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_875_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::18] 10 5 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::18]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_878_link invalid snapshot final v
 (source_after:circuit_interface [::18] 11 2 final=Some(Gval (Fuint 1) (global_word_877 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 2 final=Some(Gval (Fuint 1) (global_word_878 v)).
Proof. rewrite global_sync_878. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::18]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_878_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;18] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::18]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_881_link invalid snapshot final v
 (source_after:circuit_interface [::] 18 5 final=Some(Gval (Fuint 1) (global_word_880 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 5 final=Some(Gval (Fuint 1) (global_word_881 v)).
Proof. rewrite global_sync_881. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=18) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_881_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::18] 5 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=18) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_884_link invalid snapshot final v
 (source_after:circuit_interface [::18] 11 3 final=Some(Gval (Fuint 1) (global_word_883 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 3 final=Some(Gval (Fuint 1) (global_word_884 v)).
Proof. rewrite global_sync_884. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::18]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_884_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;18] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::18]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_895_link invalid snapshot final v
 (source_after:circuit_lookup [::11;18] 5 final=Some(Gval (Fuint 1) (global_word_894 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::18] 11 5 final=Some(Gval (Fuint 1) (global_word_895 v)).
Proof. rewrite global_sync_895. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::18]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_895_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::18] 11 5 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::18]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_898_link invalid snapshot final v
 (source_after:circuit_lookup [::18] 7 final=Some(Gval (Fuint 1) (global_word_897 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 18 7 final=Some(Gval (Fuint 1) (global_word_898 v)).
Proof. rewrite global_sync_898. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=18) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_898_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 18 7 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=18) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_902_link invalid snapshot final v
 (source_after:circuit_lookup [::10;18] 6 final=Some(Gval (Fuint 1) (global_word_901 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::18] 10 6 final=Some(Gval (Fuint 1) (global_word_902 v)).
Proof. rewrite global_sync_902. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::18]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_902_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::18] 10 6 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::18]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_905_link invalid snapshot final v
 (source_after:circuit_lookup [::18] 8 final=Some(Gval (Fuint 1) (global_word_904 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 18 8 final=Some(Gval (Fuint 1) (global_word_905 v)).
Proof. rewrite global_sync_905. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=18) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_905_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 18 8 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=18) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_909_link invalid snapshot final v
 (source_after:circuit_lookup [::11;18] 6 final=Some(Gval (Fuint 1) (global_word_908 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::18] 11 6 final=Some(Gval (Fuint 1) (global_word_909 v)).
Proof. rewrite global_sync_909. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::18]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_909_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::18] 11 6 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::18]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_912_link invalid snapshot final v
 (source_after:circuit_lookup [::18] 9 final=Some(Gval (Fuint 1) (global_word_911 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 18 9 final=Some(Gval (Fuint 1) (global_word_912 v)).
Proof. rewrite global_sync_912. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=18) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_912_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 18 9 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=18) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_915_link invalid snapshot final v
 (source_after:circuit_interface [::] 19 4 final=Some(Gval (Fuint 1) (global_word_914 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 4 final=Some(Gval (Fuint 1) (global_word_915 v)).
Proof. rewrite global_sync_915. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=19) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_915_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::19] 4 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=19) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_918_link invalid snapshot final v
 (source_after:circuit_interface [::] 19 2 final=Some(Gval (Fuint 1) (global_word_917 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 2 final=Some(Gval (Fuint 1) (global_word_918 v)).
Proof. rewrite global_sync_918. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=19) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_918_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::19] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=19) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_921_link invalid snapshot final v
 (source_after:circuit_interface [::] 19 3 final=Some(Gval (Fuint 1) (global_word_920 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 3 final=Some(Gval (Fuint 1) (global_word_921 v)).
Proof. rewrite global_sync_921. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=19) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_921_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::19] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=19) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_932_link invalid snapshot final v
 (source_after:circuit_lookup [::19] 5 final=Some(Gval (Fuint 1) (global_word_931 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 19 5 final=Some(Gval (Fuint 1) (global_word_932 v)).
Proof. rewrite global_sync_932. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=19) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_932_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 19 5 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=19) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_936_link invalid snapshot final v
 (source_after:circuit_lookup [::19] 6 final=Some(Gval (Fuint 1) (global_word_935 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 19 6 final=Some(Gval (Fuint 1) (global_word_936 v)).
Proof. rewrite global_sync_936. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=19) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_936_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 19 6 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=19) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_939_link invalid snapshot final v
 (source_after:circuit_interface [::] 20 2 final=Some(Gval (Fuint 1) (global_word_938 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::20] 2 final=Some(Gval (Fuint 1) (global_word_939 v)).
Proof. rewrite global_sync_939. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=20) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_939_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::20] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=20) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_942_link invalid snapshot final v
 (source_after:circuit_interface [::] 20 3 final=Some(Gval (Fuint 1) (global_word_941 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::20] 3 final=Some(Gval (Fuint 1) (global_word_942 v)).
Proof. rewrite global_sync_942. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=20) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_942_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::20] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=20) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_950_link invalid snapshot final v
 (source_after:circuit_lookup [::20] 4 final=Some(Gval (Fuint 1) (global_word_949 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 20 4 final=Some(Gval (Fuint 1) (global_word_950 v)).
Proof. rewrite global_sync_950. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=20) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_950_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 20 4 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=20) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_954_link invalid snapshot final v
 (source_after:circuit_lookup [::20] 5 final=Some(Gval (Fuint 1) (global_word_953 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 20 5 final=Some(Gval (Fuint 1) (global_word_954 v)).
Proof. rewrite global_sync_954. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=20) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_954_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 20 5 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=20) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_957_link invalid snapshot final v
 (source_after:circuit_interface [::] 21 2 final=Some(Gval (Fuint 1) (global_word_956 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::21] 2 final=Some(Gval (Fuint 1) (global_word_957 v)).
Proof. rewrite global_sync_957. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=21) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_957_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::21] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=21) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_960_link invalid snapshot final v
 (source_after:circuit_interface [::] 21 3 final=Some(Gval (Fuint 1) (global_word_959 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::21] 3 final=Some(Gval (Fuint 1) (global_word_960 v)).
Proof. rewrite global_sync_960. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=21) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_960_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::21] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=21) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_968_link invalid snapshot final v
 (source_after:circuit_lookup [::21] 4 final=Some(Gval (Fuint 1) (global_word_967 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 21 4 final=Some(Gval (Fuint 1) (global_word_968 v)).
Proof. rewrite global_sync_968. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=21) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_968_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 21 4 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=21) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_972_link invalid snapshot final v
 (source_after:circuit_lookup [::21] 5 final=Some(Gval (Fuint 1) (global_word_971 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 21 5 final=Some(Gval (Fuint 1) (global_word_972 v)).
Proof. rewrite global_sync_972. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=21) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_972_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 21 5 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=21) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_975_link invalid snapshot final v
 (source_after:circuit_interface [::] 22 2 final=Some(Gval (Fuint 1) (global_word_974 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::22] 2 final=Some(Gval (Fuint 1) (global_word_975 v)).
Proof. rewrite global_sync_975. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=22) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_975_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::22] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=22) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_978_link invalid snapshot final v
 (source_after:circuit_interface [::] 22 3 final=Some(Gval (Fuint 1) (global_word_977 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::22] 3 final=Some(Gval (Fuint 1) (global_word_978 v)).
Proof. rewrite global_sync_978. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=22) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_978_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::22] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=22) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_986_link invalid snapshot final v
 (source_after:circuit_lookup [::22] 4 final=Some(Gval (Fuint 1) (global_word_985 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 22 4 final=Some(Gval (Fuint 1) (global_word_986 v)).
Proof. rewrite global_sync_986. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=22) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_986_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 22 4 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=22) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_990_link invalid snapshot final v
 (source_after:circuit_lookup [::22] 5 final=Some(Gval (Fuint 1) (global_word_989 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 22 5 final=Some(Gval (Fuint 1) (global_word_990 v)).
Proof. rewrite global_sync_990. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=22) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_990_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 22 5 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=22) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_993_link invalid snapshot final v
 (source_after:circuit_interface [::] 23 2 final=Some(Gval (Fuint 1) (global_word_992 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::23] 2 final=Some(Gval (Fuint 1) (global_word_993 v)).
Proof. rewrite global_sync_993. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=23) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_993_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::23] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=23) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_996_link invalid snapshot final v
 (source_after:circuit_interface [::] 23 3 final=Some(Gval (Fuint 1) (global_word_995 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::23] 3 final=Some(Gval (Fuint 1) (global_word_996 v)).
Proof. rewrite global_sync_996. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=23) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_996_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::23] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=23) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1004_link invalid snapshot final v
 (source_after:circuit_lookup [::23] 4 final=Some(Gval (Fuint 1) (global_word_1003 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 23 4 final=Some(Gval (Fuint 1) (global_word_1004 v)).
Proof. rewrite global_sync_1004. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=23) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1004_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 23 4 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=23) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1008_link invalid snapshot final v
 (source_after:circuit_lookup [::23] 5 final=Some(Gval (Fuint 1) (global_word_1007 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 23 5 final=Some(Gval (Fuint 1) (global_word_1008 v)).
Proof. rewrite global_sync_1008. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=23) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1008_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 23 5 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=23) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1011_link invalid snapshot final v
 (source_after:circuit_interface [::] 24 2 final=Some(Gval (Fuint 1) (global_word_1010 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::24] 2 final=Some(Gval (Fuint 1) (global_word_1011 v)).
Proof. rewrite global_sync_1011. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=24) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1011_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::24] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=24) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1014_link invalid snapshot final v
 (source_after:circuit_interface [::] 24 3 final=Some(Gval (Fuint 1) (global_word_1013 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::24] 3 final=Some(Gval (Fuint 1) (global_word_1014 v)).
Proof. rewrite global_sync_1014. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=24) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1014_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::24] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=24) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1022_link invalid snapshot final v
 (source_after:circuit_lookup [::24] 4 final=Some(Gval (Fuint 1) (global_word_1021 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 24 4 final=Some(Gval (Fuint 1) (global_word_1022 v)).
Proof. rewrite global_sync_1022. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=24) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1022_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 24 4 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=24) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1026_link invalid snapshot final v
 (source_after:circuit_lookup [::24] 5 final=Some(Gval (Fuint 1) (global_word_1025 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 24 5 final=Some(Gval (Fuint 1) (global_word_1026 v)).
Proof. rewrite global_sync_1026. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=24) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1026_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 24 5 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=24) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1029_link invalid snapshot final v
 (source_after:circuit_interface [::] 25 2 final=Some(Gval (Fuint 1) (global_word_1028 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::25] 2 final=Some(Gval (Fuint 1) (global_word_1029 v)).
Proof. rewrite global_sync_1029. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=25) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1029_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::25] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=25) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1032_link invalid snapshot final v
 (source_after:circuit_interface [::] 25 3 final=Some(Gval (Fuint 1) (global_word_1031 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::25] 3 final=Some(Gval (Fuint 1) (global_word_1032 v)).
Proof. rewrite global_sync_1032. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=25) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1032_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::25] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=25) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1040_link invalid snapshot final v
 (source_after:circuit_lookup [::25] 4 final=Some(Gval (Fuint 1) (global_word_1039 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 25 4 final=Some(Gval (Fuint 1) (global_word_1040 v)).
Proof. rewrite global_sync_1040. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=25) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1040_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 25 4 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=25) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1044_link invalid snapshot final v
 (source_after:circuit_lookup [::25] 5 final=Some(Gval (Fuint 1) (global_word_1043 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 25 5 final=Some(Gval (Fuint 1) (global_word_1044 v)).
Proof. rewrite global_sync_1044. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=25) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1044_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 25 5 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=25) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1047_link invalid snapshot final v
 (source_after:circuit_interface [::] 26 2 final=Some(Gval (Fuint 1) (global_word_1046 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::26] 2 final=Some(Gval (Fuint 1) (global_word_1047 v)).
Proof. rewrite global_sync_1047. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=26) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1047_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::26] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=26) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1050_link invalid snapshot final v
 (source_after:circuit_interface [::] 26 3 final=Some(Gval (Fuint 1) (global_word_1049 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::26] 3 final=Some(Gval (Fuint 1) (global_word_1050 v)).
Proof. rewrite global_sync_1050. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=26) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1050_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::26] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=26) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1058_link invalid snapshot final v
 (source_after:circuit_lookup [::26] 4 final=Some(Gval (Fuint 1) (global_word_1057 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 26 4 final=Some(Gval (Fuint 1) (global_word_1058 v)).
Proof. rewrite global_sync_1058. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=26) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1058_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 26 4 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=26) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1062_link invalid snapshot final v
 (source_after:circuit_lookup [::26] 5 final=Some(Gval (Fuint 1) (global_word_1061 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 26 5 final=Some(Gval (Fuint 1) (global_word_1062 v)).
Proof. rewrite global_sync_1062. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=26) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1062_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 26 5 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=26) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1065_link invalid snapshot final v
 (source_after:circuit_interface [::] 27 4 final=Some(Gval (Fuint 1) (global_word_1064 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 4 final=Some(Gval (Fuint 1) (global_word_1065 v)).
Proof. rewrite global_sync_1065. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=27) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1065_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::27] 4 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=27) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1068_link invalid snapshot final v
 (source_after:circuit_interface [::] 27 2 final=Some(Gval (Fuint 1) (global_word_1067 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 2 final=Some(Gval (Fuint 1) (global_word_1068 v)).
Proof. rewrite global_sync_1068. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=27) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1068_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::27] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=27) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1071_link invalid snapshot final v
 (source_after:circuit_interface [::] 27 3 final=Some(Gval (Fuint 1) (global_word_1070 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 3 final=Some(Gval (Fuint 1) (global_word_1071 v)).
Proof. rewrite global_sync_1071. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=27) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1071_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::27] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=27) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1082_link invalid snapshot final v
 (source_after:circuit_lookup [::27] 5 final=Some(Gval (Fuint 1) (global_word_1081 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 27 5 final=Some(Gval (Fuint 1) (global_word_1082 v)).
Proof. rewrite global_sync_1082. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=27) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1082_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 27 5 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=27) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1086_link invalid snapshot final v
 (source_after:circuit_lookup [::27] 6 final=Some(Gval (Fuint 1) (global_word_1085 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 27 6 final=Some(Gval (Fuint 1) (global_word_1086 v)).
Proof. rewrite global_sync_1086. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=27) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1086_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 27 6 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=27) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1089_link invalid snapshot final v
 (source_after:circuit_interface [::] 28 4 final=Some(Gval (Fuint 1) (global_word_1088 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 4 final=Some(Gval (Fuint 1) (global_word_1089 v)).
Proof. rewrite global_sync_1089. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=28) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1089_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::28] 4 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=28) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1092_link invalid snapshot final v
 (source_after:circuit_interface [::] 28 2 final=Some(Gval (Fuint 1) (global_word_1091 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 2 final=Some(Gval (Fuint 1) (global_word_1092 v)).
Proof. rewrite global_sync_1092. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=28) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1092_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::28] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=28) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1095_link invalid snapshot final v
 (source_after:circuit_interface [::] 28 3 final=Some(Gval (Fuint 1) (global_word_1094 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 3 final=Some(Gval (Fuint 1) (global_word_1095 v)).
Proof. rewrite global_sync_1095. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=28) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1095_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::28] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=28) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1106_link invalid snapshot final v
 (source_after:circuit_lookup [::28] 5 final=Some(Gval (Fuint 1) (global_word_1105 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 28 5 final=Some(Gval (Fuint 1) (global_word_1106 v)).
Proof. rewrite global_sync_1106. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=28) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1106_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 28 5 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=28) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1110_link invalid snapshot final v
 (source_after:circuit_lookup [::28] 6 final=Some(Gval (Fuint 1) (global_word_1109 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 28 6 final=Some(Gval (Fuint 1) (global_word_1110 v)).
Proof. rewrite global_sync_1110. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=28) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1110_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 28 6 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=28) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1113_link invalid snapshot final v
 (source_after:circuit_interface [::] 29 2 final=Some(Gval (Fuint 1) (global_word_1112 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::29] 2 final=Some(Gval (Fuint 1) (global_word_1113 v)).
Proof. rewrite global_sync_1113. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=29) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1113_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::29] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=29) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1116_link invalid snapshot final v
 (source_after:circuit_interface [::] 29 3 final=Some(Gval (Fuint 1) (global_word_1115 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::29] 3 final=Some(Gval (Fuint 1) (global_word_1116 v)).
Proof. rewrite global_sync_1116. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=29) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1116_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::29] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=29) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1124_link invalid snapshot final v
 (source_after:circuit_lookup [::29] 4 final=Some(Gval (Fuint 1) (global_word_1123 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 29 4 final=Some(Gval (Fuint 1) (global_word_1124 v)).
Proof. rewrite global_sync_1124. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=29) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1124_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 29 4 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=29) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1128_link invalid snapshot final v
 (source_after:circuit_lookup [::29] 5 final=Some(Gval (Fuint 1) (global_word_1127 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 29 5 final=Some(Gval (Fuint 1) (global_word_1128 v)).
Proof. rewrite global_sync_1128. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=29) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1128_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 29 5 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=29) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1131_link invalid snapshot final v
 (source_after:circuit_interface [::] 30 2 final=Some(Gval (Fuint 1) (global_word_1130 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::30] 2 final=Some(Gval (Fuint 1) (global_word_1131 v)).
Proof. rewrite global_sync_1131. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=30) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1131_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::30] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=30) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1134_link invalid snapshot final v
 (source_after:circuit_interface [::] 30 3 final=Some(Gval (Fuint 1) (global_word_1133 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::30] 3 final=Some(Gval (Fuint 1) (global_word_1134 v)).
Proof. rewrite global_sync_1134. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=30) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1134_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::30] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=30) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1142_link invalid snapshot final v
 (source_after:circuit_lookup [::30] 4 final=Some(Gval (Fuint 1) (global_word_1141 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 30 4 final=Some(Gval (Fuint 1) (global_word_1142 v)).
Proof. rewrite global_sync_1142. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=30) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1142_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 30 4 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=30) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1146_link invalid snapshot final v
 (source_after:circuit_lookup [::30] 5 final=Some(Gval (Fuint 1) (global_word_1145 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 30 5 final=Some(Gval (Fuint 1) (global_word_1146 v)).
Proof. rewrite global_sync_1146. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=30) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1146_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 30 5 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=30) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1149_link invalid snapshot final v
 (source_after:circuit_interface [::] 31 2 final=Some(Gval (Fuint 1) (global_word_1148 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::31] 2 final=Some(Gval (Fuint 1) (global_word_1149 v)).
Proof. rewrite global_sync_1149. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=31) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1149_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::31] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=31) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1152_link invalid snapshot final v
 (source_after:circuit_interface [::] 31 3 final=Some(Gval (Fuint 1) (global_word_1151 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::31] 3 final=Some(Gval (Fuint 1) (global_word_1152 v)).
Proof. rewrite global_sync_1152. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=31) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1152_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::31] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=31) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1160_link invalid snapshot final v
 (source_after:circuit_lookup [::31] 4 final=Some(Gval (Fuint 1) (global_word_1159 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 31 4 final=Some(Gval (Fuint 1) (global_word_1160 v)).
Proof. rewrite global_sync_1160. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=31) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1160_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 31 4 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=31) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1164_link invalid snapshot final v
 (source_after:circuit_lookup [::31] 5 final=Some(Gval (Fuint 1) (global_word_1163 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 31 5 final=Some(Gval (Fuint 1) (global_word_1164 v)).
Proof. rewrite global_sync_1164. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=31) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1164_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 31 5 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=31) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1167_link invalid snapshot final v
 (source_after:circuit_interface [::] 32 2 final=Some(Gval (Fuint 1) (global_word_1166 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::32] 2 final=Some(Gval (Fuint 1) (global_word_1167 v)).
Proof. rewrite global_sync_1167. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=32) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1167_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::32] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=32) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1170_link invalid snapshot final v
 (source_after:circuit_interface [::] 32 3 final=Some(Gval (Fuint 1) (global_word_1169 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::32] 3 final=Some(Gval (Fuint 1) (global_word_1170 v)).
Proof. rewrite global_sync_1170. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=32) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1170_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::32] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=32) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1178_link invalid snapshot final v
 (source_after:circuit_lookup [::32] 4 final=Some(Gval (Fuint 1) (global_word_1177 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 32 4 final=Some(Gval (Fuint 1) (global_word_1178 v)).
Proof. rewrite global_sync_1178. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=32) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1178_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 32 4 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=32) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1182_link invalid snapshot final v
 (source_after:circuit_lookup [::32] 5 final=Some(Gval (Fuint 1) (global_word_1181 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 32 5 final=Some(Gval (Fuint 1) (global_word_1182 v)).
Proof. rewrite global_sync_1182. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=32) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1182_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 32 5 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=32) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1185_link invalid snapshot final v
 (source_after:circuit_interface [::] 33 4 final=Some(Gval (Fuint 1) (global_word_1184 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 4 final=Some(Gval (Fuint 1) (global_word_1185 v)).
Proof. rewrite global_sync_1185. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=33) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1185_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::33] 4 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=33) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1188_link invalid snapshot final v
 (source_after:circuit_interface [::] 33 2 final=Some(Gval (Fuint 1) (global_word_1187 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 2 final=Some(Gval (Fuint 1) (global_word_1188 v)).
Proof. rewrite global_sync_1188. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=33) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1188_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::33] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=33) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1191_link invalid snapshot final v
 (source_after:circuit_interface [::] 33 3 final=Some(Gval (Fuint 1) (global_word_1190 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 3 final=Some(Gval (Fuint 1) (global_word_1191 v)).
Proof. rewrite global_sync_1191. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=33) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1191_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::33] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=33) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1202_link invalid snapshot final v
 (source_after:circuit_lookup [::33] 5 final=Some(Gval (Fuint 1) (global_word_1201 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 33 5 final=Some(Gval (Fuint 1) (global_word_1202 v)).
Proof. rewrite global_sync_1202. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=33) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1202_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 33 5 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=33) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1206_link invalid snapshot final v
 (source_after:circuit_lookup [::33] 6 final=Some(Gval (Fuint 1) (global_word_1205 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 33 6 final=Some(Gval (Fuint 1) (global_word_1206 v)).
Proof. rewrite global_sync_1206. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=33) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1206_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 33 6 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=33) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1209_link invalid snapshot final v
 (source_after:circuit_interface [::] 34 2 final=Some(Gval (Fuint 1) (global_word_1208 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::34] 2 final=Some(Gval (Fuint 1) (global_word_1209 v)).
Proof. rewrite global_sync_1209. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=34) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1209_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::34] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=34) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1212_link invalid snapshot final v
 (source_after:circuit_interface [::] 34 3 final=Some(Gval (Fuint 1) (global_word_1211 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::34] 3 final=Some(Gval (Fuint 1) (global_word_1212 v)).
Proof. rewrite global_sync_1212. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=34) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1212_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::34] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=34) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1220_link invalid snapshot final v
 (source_after:circuit_lookup [::34] 4 final=Some(Gval (Fuint 1) (global_word_1219 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 34 4 final=Some(Gval (Fuint 1) (global_word_1220 v)).
Proof. rewrite global_sync_1220. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=34) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1220_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 34 4 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=34) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1224_link invalid snapshot final v
 (source_after:circuit_lookup [::34] 5 final=Some(Gval (Fuint 1) (global_word_1223 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 34 5 final=Some(Gval (Fuint 1) (global_word_1224 v)).
Proof. rewrite global_sync_1224. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=34) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1224_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 34 5 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=34) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1227_link invalid snapshot final v
 (source_after:circuit_interface [::] 35 2 final=Some(Gval (Fuint 1) (global_word_1226 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::35] 2 final=Some(Gval (Fuint 1) (global_word_1227 v)).
Proof. rewrite global_sync_1227. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=35) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1227_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::35] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=35) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1230_link invalid snapshot final v
 (source_after:circuit_interface [::] 35 3 final=Some(Gval (Fuint 1) (global_word_1229 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::35] 3 final=Some(Gval (Fuint 1) (global_word_1230 v)).
Proof. rewrite global_sync_1230. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=35) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1230_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::35] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=35) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1238_link invalid snapshot final v
 (source_after:circuit_lookup [::35] 4 final=Some(Gval (Fuint 1) (global_word_1237 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 35 4 final=Some(Gval (Fuint 1) (global_word_1238 v)).
Proof. rewrite global_sync_1238. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=35) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1238_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 35 4 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=35) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1242_link invalid snapshot final v
 (source_after:circuit_lookup [::35] 5 final=Some(Gval (Fuint 1) (global_word_1241 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 35 5 final=Some(Gval (Fuint 1) (global_word_1242 v)).
Proof. rewrite global_sync_1242. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=35) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1242_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 35 5 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=35) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1245_link invalid snapshot final v
 (source_after:circuit_interface [::] 36 2 final=Some(Gval (Fuint 1) (global_word_1244 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::36] 2 final=Some(Gval (Fuint 1) (global_word_1245 v)).
Proof. rewrite global_sync_1245. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=36) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1245_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::36] 2 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=36) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)))]) (suffix:=[::(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1248_link invalid snapshot final v
 (source_after:circuit_interface [::] 36 3 final=Some(Gval (Fuint 1) (global_word_1247 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::36] 3 final=Some(Gval (Fuint 1) (global_word_1248 v)).
Proof. rewrite global_sync_1248. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=36) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1248_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::36] 3 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=36) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1256_link invalid snapshot final v
 (source_after:circuit_lookup [::36] 4 final=Some(Gval (Fuint 1) (global_word_1255 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 36 4 final=Some(Gval (Fuint 1) (global_word_1256 v)).
Proof. rewrite global_sync_1256. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=36) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1256_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 36 4 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=36) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)))]) (suffix:=[::(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1260_link invalid snapshot final v
 (source_after:circuit_lookup [::36] 5 final=Some(Gval (Fuint 1) (global_word_1259 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 36 5 final=Some(Gval (Fuint 1) (global_word_1260 v)).
Proof. rewrite global_sync_1260. eapply circuit_pass_output_link with (instances:=multiplier_instances) (instance:=36) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1260_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface_ground [::] 36 5 (Fuint 1) final.
Proof. eapply circuit_pass_output_type with (instances:=multiplier_instances) (instance:=36) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock));(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)))]) (suffix:=[::]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1380_link invalid snapshot final v
 (source_after:circuit_interface [::] 7 1 final=Some(Gval (Fuint 1) (global_word_1311 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::7] 1 final=Some(Gval (Fuint 1) (global_word_1380 v)).
Proof. rewrite global_sync_1380. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=7) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1380_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::7] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=7) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1384_link invalid snapshot final v
 (source_after:circuit_interface [::] 7 0 final=Some(Gval Fclock (global_word_1310 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::7] 0 final=Some(Gval Fclock (global_word_1384 v)).
Proof. rewrite global_sync_1384. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=7) (parent:=[::]) (module_id:=0) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1384_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::7] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=7) (parent:=[::]) (module_id:=0) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1395_link invalid snapshot final v
 (source_after:circuit_interface [::] 8 1 final=Some(Gval (Fuint 1) (global_word_1313 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::8] 1 final=Some(Gval (Fuint 1) (global_word_1395 v)).
Proof. rewrite global_sync_1395. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=8) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1395_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::8] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=8) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1399_link invalid snapshot final v
 (source_after:circuit_interface [::] 8 0 final=Some(Gval Fclock (global_word_1312 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::8] 0 final=Some(Gval Fclock (global_word_1399 v)).
Proof. rewrite global_sync_1399. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=8) (parent:=[::]) (module_id:=0) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1399_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::8] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=8) (parent:=[::]) (module_id:=0) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1413_link invalid snapshot final v
 (source_after:circuit_interface [::] 9 1 final=Some(Gval (Fuint 1) (global_word_1315 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::9] 1 final=Some(Gval (Fuint 1) (global_word_1413 v)).
Proof. rewrite global_sync_1413. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=9) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1413_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::9] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=9) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1417_link invalid snapshot final v
 (source_after:circuit_interface [::] 9 0 final=Some(Gval Fclock (global_word_1314 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::9] 0 final=Some(Gval Fclock (global_word_1417 v)).
Proof. rewrite global_sync_1417. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=9) (parent:=[::]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1417_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::9] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=9) (parent:=[::]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1431_link invalid snapshot final v
 (source_after:circuit_interface [::] 10 1 final=Some(Gval (Fuint 1) (global_word_1317 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10] 1 final=Some(Gval (Fuint 1) (global_word_1431 v)).
Proof. rewrite global_sync_1431. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1431_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1435_link invalid snapshot final v
 (source_after:circuit_interface [::] 10 0 final=Some(Gval Fclock (global_word_1316 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10] 0 final=Some(Gval Fclock (global_word_1435 v)).
Proof. rewrite global_sync_1435. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1435_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1459_link invalid snapshot final v
 (source_after:circuit_interface [::] 11 1 final=Some(Gval (Fuint 1) (global_word_1319 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11] 1 final=Some(Gval (Fuint 1) (global_word_1459 v)).
Proof. rewrite global_sync_1459. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1459_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1463_link invalid snapshot final v
 (source_after:circuit_interface [::] 11 0 final=Some(Gval Fclock (global_word_1318 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11] 0 final=Some(Gval Fclock (global_word_1463 v)).
Proof. rewrite global_sync_1463. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::]) (module_id:=2) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1463_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::]) (module_id:=2) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1481_link invalid snapshot final v
 (source_after:circuit_interface [::11] 10 1 final=Some(Gval (Fuint 1) (global_word_1465 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;11] 1 final=Some(Gval (Fuint 1) (global_word_1481 v)).
Proof. rewrite global_sync_1481. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::11]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1481_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;11] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::11]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1485_link invalid snapshot final v
 (source_after:circuit_interface [::11] 10 0 final=Some(Gval Fclock (global_word_1464 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;11] 0 final=Some(Gval Fclock (global_word_1485 v)).
Proof. rewrite global_sync_1485. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::11]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1485_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;11] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::11]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1499_link invalid snapshot final v
 (source_after:circuit_interface [::11] 11 1 final=Some(Gval (Fuint 1) (global_word_1467 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;11] 1 final=Some(Gval (Fuint 1) (global_word_1499 v)).
Proof. rewrite global_sync_1499. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::11]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1499_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;11] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::11]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1503_link invalid snapshot final v
 (source_after:circuit_interface [::11] 11 0 final=Some(Gval Fclock (global_word_1466 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;11] 0 final=Some(Gval Fclock (global_word_1503 v)).
Proof. rewrite global_sync_1503. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::11]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1503_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;11] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::11]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1527_link invalid snapshot final v
 (source_after:circuit_interface [::] 12 1 final=Some(Gval (Fuint 1) (global_word_1321 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::12] 1 final=Some(Gval (Fuint 1) (global_word_1527 v)).
Proof. rewrite global_sync_1527. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=12) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1527_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::12] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=12) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1531_link invalid snapshot final v
 (source_after:circuit_interface [::] 12 0 final=Some(Gval Fclock (global_word_1320 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::12] 0 final=Some(Gval Fclock (global_word_1531 v)).
Proof. rewrite global_sync_1531. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=12) (parent:=[::]) (module_id:=2) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1531_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::12] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=12) (parent:=[::]) (module_id:=2) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1549_link invalid snapshot final v
 (source_after:circuit_interface [::12] 10 1 final=Some(Gval (Fuint 1) (global_word_1533 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;12] 1 final=Some(Gval (Fuint 1) (global_word_1549 v)).
Proof. rewrite global_sync_1549. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::12]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1549_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;12] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::12]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1553_link invalid snapshot final v
 (source_after:circuit_interface [::12] 10 0 final=Some(Gval Fclock (global_word_1532 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;12] 0 final=Some(Gval Fclock (global_word_1553 v)).
Proof. rewrite global_sync_1553. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::12]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1553_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;12] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::12]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1567_link invalid snapshot final v
 (source_after:circuit_interface [::12] 11 1 final=Some(Gval (Fuint 1) (global_word_1535 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;12] 1 final=Some(Gval (Fuint 1) (global_word_1567 v)).
Proof. rewrite global_sync_1567. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::12]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1567_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;12] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::12]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1571_link invalid snapshot final v
 (source_after:circuit_interface [::12] 11 0 final=Some(Gval Fclock (global_word_1534 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;12] 0 final=Some(Gval Fclock (global_word_1571 v)).
Proof. rewrite global_sync_1571. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::12]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1571_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;12] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::12]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1595_link invalid snapshot final v
 (source_after:circuit_interface [::] 13 1 final=Some(Gval (Fuint 1) (global_word_1323 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::13] 1 final=Some(Gval (Fuint 1) (global_word_1595 v)).
Proof. rewrite global_sync_1595. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=13) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1595_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::13] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=13) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1599_link invalid snapshot final v
 (source_after:circuit_interface [::] 13 0 final=Some(Gval Fclock (global_word_1322 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::13] 0 final=Some(Gval Fclock (global_word_1599 v)).
Proof. rewrite global_sync_1599. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=13) (parent:=[::]) (module_id:=2) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1599_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::13] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=13) (parent:=[::]) (module_id:=2) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1617_link invalid snapshot final v
 (source_after:circuit_interface [::13] 10 1 final=Some(Gval (Fuint 1) (global_word_1601 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;13] 1 final=Some(Gval (Fuint 1) (global_word_1617 v)).
Proof. rewrite global_sync_1617. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::13]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1617_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;13] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::13]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1621_link invalid snapshot final v
 (source_after:circuit_interface [::13] 10 0 final=Some(Gval Fclock (global_word_1600 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;13] 0 final=Some(Gval Fclock (global_word_1621 v)).
Proof. rewrite global_sync_1621. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::13]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1621_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;13] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::13]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1635_link invalid snapshot final v
 (source_after:circuit_interface [::13] 11 1 final=Some(Gval (Fuint 1) (global_word_1603 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;13] 1 final=Some(Gval (Fuint 1) (global_word_1635 v)).
Proof. rewrite global_sync_1635. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::13]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1635_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;13] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::13]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1639_link invalid snapshot final v
 (source_after:circuit_interface [::13] 11 0 final=Some(Gval Fclock (global_word_1602 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;13] 0 final=Some(Gval Fclock (global_word_1639 v)).
Proof. rewrite global_sync_1639. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::13]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1639_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;13] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::13]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1663_link invalid snapshot final v
 (source_after:circuit_interface [::] 14 1 final=Some(Gval (Fuint 1) (global_word_1325 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::14] 1 final=Some(Gval (Fuint 1) (global_word_1663 v)).
Proof. rewrite global_sync_1663. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=14) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1663_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::14] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=14) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1667_link invalid snapshot final v
 (source_after:circuit_interface [::] 14 0 final=Some(Gval Fclock (global_word_1324 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::14] 0 final=Some(Gval Fclock (global_word_1667 v)).
Proof. rewrite global_sync_1667. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=14) (parent:=[::]) (module_id:=2) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1667_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::14] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=14) (parent:=[::]) (module_id:=2) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1685_link invalid snapshot final v
 (source_after:circuit_interface [::14] 10 1 final=Some(Gval (Fuint 1) (global_word_1669 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;14] 1 final=Some(Gval (Fuint 1) (global_word_1685 v)).
Proof. rewrite global_sync_1685. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::14]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1685_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;14] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::14]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1689_link invalid snapshot final v
 (source_after:circuit_interface [::14] 10 0 final=Some(Gval Fclock (global_word_1668 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;14] 0 final=Some(Gval Fclock (global_word_1689 v)).
Proof. rewrite global_sync_1689. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::14]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1689_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;14] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::14]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1703_link invalid snapshot final v
 (source_after:circuit_interface [::14] 11 1 final=Some(Gval (Fuint 1) (global_word_1671 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;14] 1 final=Some(Gval (Fuint 1) (global_word_1703 v)).
Proof. rewrite global_sync_1703. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::14]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1703_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;14] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::14]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1707_link invalid snapshot final v
 (source_after:circuit_interface [::14] 11 0 final=Some(Gval Fclock (global_word_1670 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;14] 0 final=Some(Gval Fclock (global_word_1707 v)).
Proof. rewrite global_sync_1707. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::14]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1707_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;14] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::14]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1731_link invalid snapshot final v
 (source_after:circuit_interface [::] 15 1 final=Some(Gval (Fuint 1) (global_word_1327 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::15] 1 final=Some(Gval (Fuint 1) (global_word_1731 v)).
Proof. rewrite global_sync_1731. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=15) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1731_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::15] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=15) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1735_link invalid snapshot final v
 (source_after:circuit_interface [::] 15 0 final=Some(Gval Fclock (global_word_1326 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::15] 0 final=Some(Gval Fclock (global_word_1735 v)).
Proof. rewrite global_sync_1735. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=15) (parent:=[::]) (module_id:=2) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1735_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::15] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=15) (parent:=[::]) (module_id:=2) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1753_link invalid snapshot final v
 (source_after:circuit_interface [::15] 10 1 final=Some(Gval (Fuint 1) (global_word_1737 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;15] 1 final=Some(Gval (Fuint 1) (global_word_1753 v)).
Proof. rewrite global_sync_1753. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::15]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1753_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;15] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::15]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1757_link invalid snapshot final v
 (source_after:circuit_interface [::15] 10 0 final=Some(Gval Fclock (global_word_1736 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;15] 0 final=Some(Gval Fclock (global_word_1757 v)).
Proof. rewrite global_sync_1757. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::15]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1757_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;15] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::15]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1771_link invalid snapshot final v
 (source_after:circuit_interface [::15] 11 1 final=Some(Gval (Fuint 1) (global_word_1739 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;15] 1 final=Some(Gval (Fuint 1) (global_word_1771 v)).
Proof. rewrite global_sync_1771. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::15]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1771_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;15] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::15]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1775_link invalid snapshot final v
 (source_after:circuit_interface [::15] 11 0 final=Some(Gval Fclock (global_word_1738 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;15] 0 final=Some(Gval Fclock (global_word_1775 v)).
Proof. rewrite global_sync_1775. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::15]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1775_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;15] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::15]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1799_link invalid snapshot final v
 (source_after:circuit_interface [::] 16 1 final=Some(Gval (Fuint 1) (global_word_1329 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::16] 1 final=Some(Gval (Fuint 1) (global_word_1799 v)).
Proof. rewrite global_sync_1799. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=16) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1799_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::16] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=16) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1803_link invalid snapshot final v
 (source_after:circuit_interface [::] 16 0 final=Some(Gval Fclock (global_word_1328 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::16] 0 final=Some(Gval Fclock (global_word_1803 v)).
Proof. rewrite global_sync_1803. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=16) (parent:=[::]) (module_id:=2) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1803_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::16] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=16) (parent:=[::]) (module_id:=2) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1821_link invalid snapshot final v
 (source_after:circuit_interface [::16] 10 1 final=Some(Gval (Fuint 1) (global_word_1805 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 1 final=Some(Gval (Fuint 1) (global_word_1821 v)).
Proof. rewrite global_sync_1821. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::16]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1821_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;16] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::16]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1825_link invalid snapshot final v
 (source_after:circuit_interface [::16] 10 0 final=Some(Gval Fclock (global_word_1804 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;16] 0 final=Some(Gval Fclock (global_word_1825 v)).
Proof. rewrite global_sync_1825. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::16]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1825_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;16] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::16]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1839_link invalid snapshot final v
 (source_after:circuit_interface [::16] 11 1 final=Some(Gval (Fuint 1) (global_word_1807 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 1 final=Some(Gval (Fuint 1) (global_word_1839 v)).
Proof. rewrite global_sync_1839. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::16]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1839_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;16] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::16]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1843_link invalid snapshot final v
 (source_after:circuit_interface [::16] 11 0 final=Some(Gval Fclock (global_word_1806 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;16] 0 final=Some(Gval Fclock (global_word_1843 v)).
Proof. rewrite global_sync_1843. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::16]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1843_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;16] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::16]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1867_link invalid snapshot final v
 (source_after:circuit_interface [::] 17 1 final=Some(Gval (Fuint 1) (global_word_1331 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 1 final=Some(Gval (Fuint 1) (global_word_1867 v)).
Proof. rewrite global_sync_1867. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=17) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1867_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::17] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=17) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1871_link invalid snapshot final v
 (source_after:circuit_interface [::] 17 0 final=Some(Gval Fclock (global_word_1330 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::17] 0 final=Some(Gval Fclock (global_word_1871 v)).
Proof. rewrite global_sync_1871. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=17) (parent:=[::]) (module_id:=2) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1871_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::17] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=17) (parent:=[::]) (module_id:=2) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1889_link invalid snapshot final v
 (source_after:circuit_interface [::17] 10 1 final=Some(Gval (Fuint 1) (global_word_1873 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 1 final=Some(Gval (Fuint 1) (global_word_1889 v)).
Proof. rewrite global_sync_1889. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::17]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1889_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;17] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::17]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1893_link invalid snapshot final v
 (source_after:circuit_interface [::17] 10 0 final=Some(Gval Fclock (global_word_1872 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;17] 0 final=Some(Gval Fclock (global_word_1893 v)).
Proof. rewrite global_sync_1893. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::17]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1893_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;17] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::17]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1907_link invalid snapshot final v
 (source_after:circuit_interface [::17] 11 1 final=Some(Gval (Fuint 1) (global_word_1875 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 1 final=Some(Gval (Fuint 1) (global_word_1907 v)).
Proof. rewrite global_sync_1907. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::17]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1907_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;17] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::17]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1911_link invalid snapshot final v
 (source_after:circuit_interface [::17] 11 0 final=Some(Gval Fclock (global_word_1874 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;17] 0 final=Some(Gval Fclock (global_word_1911 v)).
Proof. rewrite global_sync_1911. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::17]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1911_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;17] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::17]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1935_link invalid snapshot final v
 (source_after:circuit_interface [::] 18 1 final=Some(Gval (Fuint 1) (global_word_1333 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 1 final=Some(Gval (Fuint 1) (global_word_1935 v)).
Proof. rewrite global_sync_1935. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=18) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1935_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::18] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=18) (parent:=[::]) (module_id:=2) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1939_link invalid snapshot final v
 (source_after:circuit_interface [::] 18 0 final=Some(Gval Fclock (global_word_1332 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::18] 0 final=Some(Gval Fclock (global_word_1939 v)).
Proof. rewrite global_sync_1939. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=18) (parent:=[::]) (module_id:=2) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1939_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::18] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=18) (parent:=[::]) (module_id:=2) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Finput VarOrder.T 5 (Gtyp (Fuint 1)));(@Finput VarOrder.T 6 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 7 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 8 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 9 (Gtyp (Fuint 1)))]) (body:=generated_module_2_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1957_link invalid snapshot final v
 (source_after:circuit_interface [::18] 10 1 final=Some(Gval (Fuint 1) (global_word_1941 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 1 final=Some(Gval (Fuint 1) (global_word_1957 v)).
Proof. rewrite global_sync_1957. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::18]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1957_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;18] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::18]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1961_link invalid snapshot final v
 (source_after:circuit_interface [::18] 10 0 final=Some(Gval Fclock (global_word_1940 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;18] 0 final=Some(Gval Fclock (global_word_1961 v)).
Proof. rewrite global_sync_1961. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=10) (parent:=[::18]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1961_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::10;18] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=10) (parent:=[::18]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1975_link invalid snapshot final v
 (source_after:circuit_interface [::18] 11 1 final=Some(Gval (Fuint 1) (global_word_1943 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 1 final=Some(Gval (Fuint 1) (global_word_1975 v)).
Proof. rewrite global_sync_1975. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::18]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1975_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;18] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::18]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1979_link invalid snapshot final v
 (source_after:circuit_interface [::18] 11 0 final=Some(Gval Fclock (global_word_1942 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;18] 0 final=Some(Gval Fclock (global_word_1979 v)).
Proof. rewrite global_sync_1979. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=11) (parent:=[::18]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1979_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::11;18] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=11) (parent:=[::18]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1993_link invalid snapshot final v
 (source_after:circuit_interface [::] 19 1 final=Some(Gval (Fuint 1) (global_word_1335 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 1 final=Some(Gval (Fuint 1) (global_word_1993 v)).
Proof. rewrite global_sync_1993. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=19) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1993_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::19] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=19) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_1997_link invalid snapshot final v
 (source_after:circuit_interface [::] 19 0 final=Some(Gval Fclock (global_word_1334 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::19] 0 final=Some(Gval Fclock (global_word_1997 v)).
Proof. rewrite global_sync_1997. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=19) (parent:=[::]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_1997_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::19] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=19) (parent:=[::]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_2008_link invalid snapshot final v
 (source_after:circuit_interface [::] 20 1 final=Some(Gval (Fuint 1) (global_word_1337 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::20] 1 final=Some(Gval (Fuint 1) (global_word_2008 v)).
Proof. rewrite global_sync_2008. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=20) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_2008_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::20] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=20) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_2012_link invalid snapshot final v
 (source_after:circuit_interface [::] 20 0 final=Some(Gval Fclock (global_word_1336 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::20] 0 final=Some(Gval Fclock (global_word_2012 v)).
Proof. rewrite global_sync_2012. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=20) (parent:=[::]) (module_id:=0) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_2012_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::20] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=20) (parent:=[::]) (module_id:=0) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_2023_link invalid snapshot final v
 (source_after:circuit_interface [::] 21 1 final=Some(Gval (Fuint 1) (global_word_1339 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::21] 1 final=Some(Gval (Fuint 1) (global_word_2023 v)).
Proof. rewrite global_sync_2023. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=21) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_2023_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::21] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=21) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_2027_link invalid snapshot final v
 (source_after:circuit_interface [::] 21 0 final=Some(Gval Fclock (global_word_1338 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::21] 0 final=Some(Gval Fclock (global_word_2027 v)).
Proof. rewrite global_sync_2027. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=21) (parent:=[::]) (module_id:=0) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_2027_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::21] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=21) (parent:=[::]) (module_id:=0) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_2038_link invalid snapshot final v
 (source_after:circuit_interface [::] 22 1 final=Some(Gval (Fuint 1) (global_word_1341 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::22] 1 final=Some(Gval (Fuint 1) (global_word_2038 v)).
Proof. rewrite global_sync_2038. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=22) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_2038_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::22] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=22) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_2042_link invalid snapshot final v
 (source_after:circuit_interface [::] 22 0 final=Some(Gval Fclock (global_word_1340 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::22] 0 final=Some(Gval Fclock (global_word_2042 v)).
Proof. rewrite global_sync_2042. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=22) (parent:=[::]) (module_id:=0) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_2042_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::22] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=22) (parent:=[::]) (module_id:=0) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_2053_link invalid snapshot final v
 (source_after:circuit_interface [::] 23 1 final=Some(Gval (Fuint 1) (global_word_1343 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::23] 1 final=Some(Gval (Fuint 1) (global_word_2053 v)).
Proof. rewrite global_sync_2053. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=23) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_2053_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::23] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=23) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_2057_link invalid snapshot final v
 (source_after:circuit_interface [::] 23 0 final=Some(Gval Fclock (global_word_1342 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::23] 0 final=Some(Gval Fclock (global_word_2057 v)).
Proof. rewrite global_sync_2057. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=23) (parent:=[::]) (module_id:=0) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_2057_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::23] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=23) (parent:=[::]) (module_id:=0) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_2068_link invalid snapshot final v
 (source_after:circuit_interface [::] 24 1 final=Some(Gval (Fuint 1) (global_word_1345 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::24] 1 final=Some(Gval (Fuint 1) (global_word_2068 v)).
Proof. rewrite global_sync_2068. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=24) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_2068_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::24] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=24) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_2072_link invalid snapshot final v
 (source_after:circuit_interface [::] 24 0 final=Some(Gval Fclock (global_word_1344 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::24] 0 final=Some(Gval Fclock (global_word_2072 v)).
Proof. rewrite global_sync_2072. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=24) (parent:=[::]) (module_id:=0) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_2072_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::24] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=24) (parent:=[::]) (module_id:=0) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_2083_link invalid snapshot final v
 (source_after:circuit_interface [::] 25 1 final=Some(Gval (Fuint 1) (global_word_1347 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::25] 1 final=Some(Gval (Fuint 1) (global_word_2083 v)).
Proof. rewrite global_sync_2083. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=25) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_2083_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::25] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=25) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_2087_link invalid snapshot final v
 (source_after:circuit_interface [::] 25 0 final=Some(Gval Fclock (global_word_1346 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::25] 0 final=Some(Gval Fclock (global_word_2087 v)).
Proof. rewrite global_sync_2087. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=25) (parent:=[::]) (module_id:=0) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_2087_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::25] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=25) (parent:=[::]) (module_id:=0) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_2098_link invalid snapshot final v
 (source_after:circuit_interface [::] 26 1 final=Some(Gval (Fuint 1) (global_word_1349 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::26] 1 final=Some(Gval (Fuint 1) (global_word_2098 v)).
Proof. rewrite global_sync_2098. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=26) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_2098_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::26] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=26) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_2102_link invalid snapshot final v
 (source_after:circuit_interface [::] 26 0 final=Some(Gval Fclock (global_word_1348 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::26] 0 final=Some(Gval Fclock (global_word_2102 v)).
Proof. rewrite global_sync_2102. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=26) (parent:=[::]) (module_id:=0) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_2102_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::26] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=26) (parent:=[::]) (module_id:=0) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_2116_link invalid snapshot final v
 (source_after:circuit_interface [::] 27 1 final=Some(Gval (Fuint 1) (global_word_1351 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 1 final=Some(Gval (Fuint 1) (global_word_2116 v)).
Proof. rewrite global_sync_2116. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=27) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_2116_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::27] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=27) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_2120_link invalid snapshot final v
 (source_after:circuit_interface [::] 27 0 final=Some(Gval Fclock (global_word_1350 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::27] 0 final=Some(Gval Fclock (global_word_2120 v)).
Proof. rewrite global_sync_2120. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=27) (parent:=[::]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_2120_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::27] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=27) (parent:=[::]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_2134_link invalid snapshot final v
 (source_after:circuit_interface [::] 28 1 final=Some(Gval (Fuint 1) (global_word_1353 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 1 final=Some(Gval (Fuint 1) (global_word_2134 v)).
Proof. rewrite global_sync_2134. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=28) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_2134_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::28] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=28) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_2138_link invalid snapshot final v
 (source_after:circuit_interface [::] 28 0 final=Some(Gval Fclock (global_word_1352 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::28] 0 final=Some(Gval Fclock (global_word_2138 v)).
Proof. rewrite global_sync_2138. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=28) (parent:=[::]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_2138_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::28] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=28) (parent:=[::]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_2149_link invalid snapshot final v
 (source_after:circuit_interface [::] 29 1 final=Some(Gval (Fuint 1) (global_word_1355 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::29] 1 final=Some(Gval (Fuint 1) (global_word_2149 v)).
Proof. rewrite global_sync_2149. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=29) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_2149_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::29] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=29) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_2153_link invalid snapshot final v
 (source_after:circuit_interface [::] 29 0 final=Some(Gval Fclock (global_word_1354 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::29] 0 final=Some(Gval Fclock (global_word_2153 v)).
Proof. rewrite global_sync_2153. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=29) (parent:=[::]) (module_id:=0) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_2153_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::29] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=29) (parent:=[::]) (module_id:=0) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_2164_link invalid snapshot final v
 (source_after:circuit_interface [::] 30 1 final=Some(Gval (Fuint 1) (global_word_1357 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::30] 1 final=Some(Gval (Fuint 1) (global_word_2164 v)).
Proof. rewrite global_sync_2164. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=30) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_2164_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::30] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=30) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_2168_link invalid snapshot final v
 (source_after:circuit_interface [::] 30 0 final=Some(Gval Fclock (global_word_1356 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::30] 0 final=Some(Gval Fclock (global_word_2168 v)).
Proof. rewrite global_sync_2168. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=30) (parent:=[::]) (module_id:=0) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_2168_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::30] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=30) (parent:=[::]) (module_id:=0) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_2179_link invalid snapshot final v
 (source_after:circuit_interface [::] 31 1 final=Some(Gval (Fuint 1) (global_word_1359 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::31] 1 final=Some(Gval (Fuint 1) (global_word_2179 v)).
Proof. rewrite global_sync_2179. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=31) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_2179_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::31] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=31) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_2183_link invalid snapshot final v
 (source_after:circuit_interface [::] 31 0 final=Some(Gval Fclock (global_word_1358 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::31] 0 final=Some(Gval Fclock (global_word_2183 v)).
Proof. rewrite global_sync_2183. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=31) (parent:=[::]) (module_id:=0) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_2183_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::31] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=31) (parent:=[::]) (module_id:=0) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_2194_link invalid snapshot final v
 (source_after:circuit_interface [::] 32 1 final=Some(Gval (Fuint 1) (global_word_1361 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::32] 1 final=Some(Gval (Fuint 1) (global_word_2194 v)).
Proof. rewrite global_sync_2194. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=32) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_2194_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::32] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=32) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_2198_link invalid snapshot final v
 (source_after:circuit_interface [::] 32 0 final=Some(Gval Fclock (global_word_1360 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::32] 0 final=Some(Gval Fclock (global_word_2198 v)).
Proof. rewrite global_sync_2198. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=32) (parent:=[::]) (module_id:=0) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_2198_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::32] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=32) (parent:=[::]) (module_id:=0) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_2212_link invalid snapshot final v
 (source_after:circuit_interface [::] 33 1 final=Some(Gval (Fuint 1) (global_word_1363 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 1 final=Some(Gval (Fuint 1) (global_word_2212 v)).
Proof. rewrite global_sync_2212. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=33) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_2212_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::33] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=33) (parent:=[::]) (module_id:=1) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_2216_link invalid snapshot final v
 (source_after:circuit_interface [::] 33 0 final=Some(Gval Fclock (global_word_1362 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::33] 0 final=Some(Gval Fclock (global_word_2216 v)).
Proof. rewrite global_sync_2216. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=33) (parent:=[::]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_2216_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::33] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=33) (parent:=[::]) (module_id:=1) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Finput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 6 (Gtyp (Fuint 1)))]) (body:=generated_module_1_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_2227_link invalid snapshot final v
 (source_after:circuit_interface [::] 34 1 final=Some(Gval (Fuint 1) (global_word_1365 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::34] 1 final=Some(Gval (Fuint 1) (global_word_2227 v)).
Proof. rewrite global_sync_2227. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=34) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_2227_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::34] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=34) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_2231_link invalid snapshot final v
 (source_after:circuit_interface [::] 34 0 final=Some(Gval Fclock (global_word_1364 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::34] 0 final=Some(Gval Fclock (global_word_2231 v)).
Proof. rewrite global_sync_2231. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=34) (parent:=[::]) (module_id:=0) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_2231_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::34] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=34) (parent:=[::]) (module_id:=0) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_2242_link invalid snapshot final v
 (source_after:circuit_interface [::] 35 1 final=Some(Gval (Fuint 1) (global_word_1367 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::35] 1 final=Some(Gval (Fuint 1) (global_word_2242 v)).
Proof. rewrite global_sync_2242. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=35) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_2242_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::35] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=35) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_2246_link invalid snapshot final v
 (source_after:circuit_interface [::] 35 0 final=Some(Gval Fclock (global_word_1366 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::35] 0 final=Some(Gval Fclock (global_word_2246 v)).
Proof. rewrite global_sync_2246. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=35) (parent:=[::]) (module_id:=0) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_2246_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::35] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=35) (parent:=[::]) (module_id:=0) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_2257_link invalid snapshot final v
 (source_after:circuit_interface [::] 36 1 final=Some(Gval (Fuint 1) (global_word_1369 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::36] 1 final=Some(Gval (Fuint 1) (global_word_2257 v)).
Proof. rewrite global_sync_2257. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=36) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_2257_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::36] 1 (Fuint 1) final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=36) (parent:=[::]) (module_id:=0) (prefix:=[::(@Finput VarOrder.T 0 (Gtyp Fclock))]) (suffix:=[::(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
Lemma global_sync_2261_link invalid snapshot final v
 (source_after:circuit_interface [::] 36 0 final=Some(Gval Fclock (global_word_1368 v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::36] 0 final=Some(Gval Fclock (global_word_2261 v)).
Proof. rewrite global_sync_2261. eapply circuit_pass_input_link with (instances:=multiplier_instances) (instance:=36) (parent:=[::]) (module_id:=0) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_2261_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_value_ground [::36] 0 Fclock final.
Proof. eapply circuit_pass_input_type with (instances:=multiplier_instances) (instance:=36) (parent:=[::]) (module_id:=0) (prefix:=[::]) (suffix:=[::(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));(@Finput VarOrder.T 3 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)));(@Foutput VarOrder.T 5 (Gtyp (Fuint 1)))]) (body:=generated_module_0_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.
