From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import StatementFacts GroundFrames HierarchyFacts GlobalLocalFacts.
From SmallMultiplier Require Import Model GlobalStable GlobalInstances FlatRegisterCheck InstanceChecks.
Local Open Scope N_scope.
Lemma global_leaf_0_sync : node_sync_check generated_modules multiplier_instances [::] 0=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_0_preserved invalid snapshot final value
 (known:circuit_lookup [::] 0 snapshot=Some value)
 (typed:type_of_val value=Gtyp Fclock)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 0 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_preserves_ground with (stmts:=generated_module_3_stmts_0); [vm_compute;reflexivity|vm_compute;reflexivity|exact typed|exact known|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_0_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_0_sync).
 - exact ran.
Qed.
Lemma global_leaf_1_sync : node_sync_check generated_modules multiplier_instances [::] 1=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_1_preserved invalid snapshot final value
 (known:circuit_lookup [::] 1 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 1 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_preserves_ground with (stmts:=generated_module_3_stmts_0); [vm_compute;reflexivity|vm_compute;reflexivity|exact typed|exact known|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_1_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_1_sync).
 - exact ran.
Qed.
Lemma global_leaf_2_sync : node_sync_check generated_modules multiplier_instances [::] 2=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_2_preserved invalid snapshot final value
 (known:circuit_lookup [::] 2 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 8))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 2 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_preserves_ground with (stmts:=generated_module_3_stmts_0); [vm_compute;reflexivity|vm_compute;reflexivity|exact typed|exact known|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_2_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_2_sync).
 - exact ran.
Qed.
Lemma global_leaf_3_sync : node_sync_check generated_modules multiplier_instances [::] 201=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_3_register : flat_register_certificate 201 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_3_preserved invalid snapshot final value
 (known:circuit_lookup [::] 201 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 201 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_3_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_3_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_3_sync).
 - exact ran.
Qed.
Lemma global_leaf_4_sync : node_sync_check generated_modules multiplier_instances [::] 203=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_4_register : flat_register_certificate 203 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_4_preserved invalid snapshot final value
 (known:circuit_lookup [::] 203 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 203 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_4_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_4_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_4_sync).
 - exact ran.
Qed.
Lemma global_leaf_5_sync : node_sync_check generated_modules multiplier_instances [::] 205=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_5_register : flat_register_certificate 205 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_5_preserved invalid snapshot final value
 (known:circuit_lookup [::] 205 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 205 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_5_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_5_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_5_sync).
 - exact ran.
Qed.
Lemma global_leaf_6_sync : node_sync_check generated_modules multiplier_instances [::] 207=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_6_register : flat_register_certificate 207 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_6_preserved invalid snapshot final value
 (known:circuit_lookup [::] 207 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 207 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_6_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_6_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_6_sync).
 - exact ran.
Qed.
Lemma global_leaf_7_sync : node_sync_check generated_modules multiplier_instances [::] 209=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_7_register : flat_register_certificate 209 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_7_preserved invalid snapshot final value
 (known:circuit_lookup [::] 209 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 209 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_7_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_7_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_7_sync).
 - exact ran.
Qed.
Lemma global_leaf_8_sync : node_sync_check generated_modules multiplier_instances [::] 211=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_8_register : flat_register_certificate 211 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_8_preserved invalid snapshot final value
 (known:circuit_lookup [::] 211 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 211 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_8_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_8_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_8_sync).
 - exact ran.
Qed.
Lemma global_leaf_9_sync : node_sync_check generated_modules multiplier_instances [::] 213=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_9_register : flat_register_certificate 213 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_9_preserved invalid snapshot final value
 (known:circuit_lookup [::] 213 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 213 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_9_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_9_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_9_sync).
 - exact ran.
Qed.
Lemma global_leaf_10_sync : node_sync_check generated_modules multiplier_instances [::] 215=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_10_register : flat_register_certificate 215 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_10_preserved invalid snapshot final value
 (known:circuit_lookup [::] 215 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 215 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_10_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_10_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_10_sync).
 - exact ran.
Qed.
Lemma global_leaf_11_sync : node_sync_check generated_modules multiplier_instances [::] 217=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_11_register : flat_register_certificate 217 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_11_preserved invalid snapshot final value
 (known:circuit_lookup [::] 217 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 217 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_11_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_11_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_11_sync).
 - exact ran.
Qed.
Lemma global_leaf_12_sync : node_sync_check generated_modules multiplier_instances [::] 219=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_12_register : flat_register_certificate 219 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_12_preserved invalid snapshot final value
 (known:circuit_lookup [::] 219 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 219 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_12_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_12_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_12_sync).
 - exact ran.
Qed.
Lemma global_leaf_13_sync : node_sync_check generated_modules multiplier_instances [::] 221=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_13_register : flat_register_certificate 221 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_13_preserved invalid snapshot final value
 (known:circuit_lookup [::] 221 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 221 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_13_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_13_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_13_sync).
 - exact ran.
Qed.
Lemma global_leaf_14_sync : node_sync_check generated_modules multiplier_instances [::] 223=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_14_register : flat_register_certificate 223 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_14_preserved invalid snapshot final value
 (known:circuit_lookup [::] 223 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 223 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_14_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_14_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_14_sync).
 - exact ran.
Qed.
Lemma global_leaf_15_sync : node_sync_check generated_modules multiplier_instances [::] 225=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_15_register : flat_register_certificate 225 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_15_preserved invalid snapshot final value
 (known:circuit_lookup [::] 225 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 225 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_15_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_15_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_15_sync).
 - exact ran.
Qed.
Lemma global_leaf_16_sync : node_sync_check generated_modules multiplier_instances [::] 227=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_16_register : flat_register_certificate 227 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_16_preserved invalid snapshot final value
 (known:circuit_lookup [::] 227 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 227 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_16_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_16_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_16_sync).
 - exact ran.
Qed.
Lemma global_leaf_17_sync : node_sync_check generated_modules multiplier_instances [::] 229=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_17_register : flat_register_certificate 229 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_17_preserved invalid snapshot final value
 (known:circuit_lookup [::] 229 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 229 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_17_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_17_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_17_sync).
 - exact ran.
Qed.
Lemma global_leaf_18_sync : node_sync_check generated_modules multiplier_instances [::] 231=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_18_register : flat_register_certificate 231 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_18_preserved invalid snapshot final value
 (known:circuit_lookup [::] 231 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 231 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_18_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_18_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_18_sync).
 - exact ran.
Qed.
Lemma global_leaf_19_sync : node_sync_check generated_modules multiplier_instances [::] 233=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_19_register : flat_register_certificate 233 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_19_preserved invalid snapshot final value
 (known:circuit_lookup [::] 233 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 233 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_19_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_19_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_19_sync).
 - exact ran.
Qed.
Lemma global_leaf_20_sync : node_sync_check generated_modules multiplier_instances [::] 235=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_20_register : flat_register_certificate 235 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_20_preserved invalid snapshot final value
 (known:circuit_lookup [::] 235 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 235 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_20_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_20_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_20_sync).
 - exact ran.
Qed.
Lemma global_leaf_21_sync : node_sync_check generated_modules multiplier_instances [::] 237=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_21_register : flat_register_certificate 237 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_21_preserved invalid snapshot final value
 (known:circuit_lookup [::] 237 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 237 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_21_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_21_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_21_sync).
 - exact ran.
Qed.
Lemma global_leaf_22_sync : node_sync_check generated_modules multiplier_instances [::] 239=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_22_register : flat_register_certificate 239 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_22_preserved invalid snapshot final value
 (known:circuit_lookup [::] 239 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 239 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_22_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_22_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_22_sync).
 - exact ran.
Qed.
Lemma global_leaf_23_sync : node_sync_check generated_modules multiplier_instances [::] 241=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_23_register : flat_register_certificate 241 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_23_preserved invalid snapshot final value
 (known:circuit_lookup [::] 241 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 241 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_23_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_23_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_23_sync).
 - exact ran.
Qed.
Lemma global_leaf_24_sync : node_sync_check generated_modules multiplier_instances [::] 243=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_24_register : flat_register_certificate 243 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_24_preserved invalid snapshot final value
 (known:circuit_lookup [::] 243 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 243 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_24_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_24_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_24_sync).
 - exact ran.
Qed.
Lemma global_leaf_25_sync : node_sync_check generated_modules multiplier_instances [::] 245=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_25_register : flat_register_certificate 245 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_25_preserved invalid snapshot final value
 (known:circuit_lookup [::] 245 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 245 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_25_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_25_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_25_sync).
 - exact ran.
Qed.
Lemma global_leaf_26_sync : node_sync_check generated_modules multiplier_instances [::] 247=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_26_register : flat_register_certificate 247 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_26_preserved invalid snapshot final value
 (known:circuit_lookup [::] 247 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 247 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_26_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_26_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_26_sync).
 - exact ran.
Qed.
Lemma global_leaf_27_sync : node_sync_check generated_modules multiplier_instances [::] 249=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_27_register : flat_register_certificate 249 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_27_preserved invalid snapshot final value
 (known:circuit_lookup [::] 249 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 249 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_27_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_27_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_27_sync).
 - exact ran.
Qed.
Lemma global_leaf_28_sync : node_sync_check generated_modules multiplier_instances [::] 251=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_28_register : flat_register_certificate 251 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_28_preserved invalid snapshot final value
 (known:circuit_lookup [::] 251 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 251 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_28_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_28_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_28_sync).
 - exact ran.
Qed.
Lemma global_leaf_29_sync : node_sync_check generated_modules multiplier_instances [::] 253=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_29_register : flat_register_certificate 253 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_29_preserved invalid snapshot final value
 (known:circuit_lookup [::] 253 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 253 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_29_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_29_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_29_sync).
 - exact ran.
Qed.
Lemma global_leaf_30_sync : node_sync_check generated_modules multiplier_instances [::] 255=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_30_register : flat_register_certificate 255 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_30_preserved invalid snapshot final value
 (known:circuit_lookup [::] 255 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 255 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_30_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_30_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_30_sync).
 - exact ran.
Qed.
Lemma global_leaf_31_sync : node_sync_check generated_modules multiplier_instances [::] 257=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_31_register : flat_register_certificate 257 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_31_preserved invalid snapshot final value
 (known:circuit_lookup [::] 257 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 257 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_31_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_31_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_31_sync).
 - exact ran.
Qed.
Lemma global_leaf_32_sync : node_sync_check generated_modules multiplier_instances [::] 259=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_32_register : flat_register_certificate 259 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_32_preserved invalid snapshot final value
 (known:circuit_lookup [::] 259 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 259 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_32_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_32_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_32_sync).
 - exact ran.
Qed.
Lemma global_leaf_33_sync : node_sync_check generated_modules multiplier_instances [::] 261=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_33_register : flat_register_certificate 261 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_33_preserved invalid snapshot final value
 (known:circuit_lookup [::] 261 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 261 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_33_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_33_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_33_sync).
 - exact ran.
Qed.
Lemma global_leaf_34_sync : node_sync_check generated_modules multiplier_instances [::] 263=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_34_register : flat_register_certificate 263 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_34_preserved invalid snapshot final value
 (known:circuit_lookup [::] 263 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 263 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_34_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_34_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_34_sync).
 - exact ran.
Qed.
Lemma global_leaf_35_sync : node_sync_check generated_modules multiplier_instances [::] 265=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_35_register : flat_register_certificate 265 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_35_preserved invalid snapshot final value
 (known:circuit_lookup [::] 265 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 265 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_35_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_35_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_35_sync).
 - exact ran.
Qed.
Lemma global_leaf_36_sync : node_sync_check generated_modules multiplier_instances [::] 267=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_36_register : flat_register_certificate 267 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_36_preserved invalid snapshot final value
 (known:circuit_lookup [::] 267 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 267 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_36_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_36_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_36_sync).
 - exact ran.
Qed.
Lemma global_leaf_37_sync : node_sync_check generated_modules multiplier_instances [::] 269=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_37_register : flat_register_certificate 269 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_37_preserved invalid snapshot final value
 (known:circuit_lookup [::] 269 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 269 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_37_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_37_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_37_sync).
 - exact ran.
Qed.
Lemma global_leaf_38_sync : node_sync_check generated_modules multiplier_instances [::] 271=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_38_register : flat_register_certificate 271 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_38_preserved invalid snapshot final value
 (known:circuit_lookup [::] 271 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 271 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_38_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_38_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_38_sync).
 - exact ran.
Qed.
Lemma global_leaf_39_sync : node_sync_check generated_modules multiplier_instances [::] 273=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_39_register : flat_register_certificate 273 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_39_preserved invalid snapshot final value
 (known:circuit_lookup [::] 273 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 273 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_39_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_39_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_39_sync).
 - exact ran.
Qed.
Lemma global_leaf_40_sync : node_sync_check generated_modules multiplier_instances [::] 275=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_40_register : flat_register_certificate 275 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_40_preserved invalid snapshot final value
 (known:circuit_lookup [::] 275 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 275 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_40_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_40_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_40_sync).
 - exact ran.
Qed.
Lemma global_leaf_41_sync : node_sync_check generated_modules multiplier_instances [::] 277=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_41_register : flat_register_certificate 277 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_41_preserved invalid snapshot final value
 (known:circuit_lookup [::] 277 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 277 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_41_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_41_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_41_sync).
 - exact ran.
Qed.
Lemma global_leaf_42_sync : node_sync_check generated_modules multiplier_instances [::] 279=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_42_register : flat_register_certificate 279 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_42_preserved invalid snapshot final value
 (known:circuit_lookup [::] 279 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 279 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_42_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_42_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_42_sync).
 - exact ran.
Qed.
Lemma global_leaf_43_sync : node_sync_check generated_modules multiplier_instances [::] 281=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_43_register : flat_register_certificate 281 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_43_preserved invalid snapshot final value
 (known:circuit_lookup [::] 281 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 281 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_43_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_43_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_43_sync).
 - exact ran.
Qed.
Lemma global_leaf_44_sync : node_sync_check generated_modules multiplier_instances [::] 283=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_44_register : flat_register_certificate 283 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_44_preserved invalid snapshot final value
 (known:circuit_lookup [::] 283 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 283 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_44_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_44_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_44_sync).
 - exact ran.
Qed.
Lemma global_leaf_45_sync : node_sync_check generated_modules multiplier_instances [::] 285=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_45_register : flat_register_certificate 285 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_45_preserved invalid snapshot final value
 (known:circuit_lookup [::] 285 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 285 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_45_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_45_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_45_sync).
 - exact ran.
Qed.
Lemma global_leaf_46_sync : node_sync_check generated_modules multiplier_instances [::] 287=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_46_register : flat_register_certificate 287 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_46_preserved invalid snapshot final value
 (known:circuit_lookup [::] 287 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 287 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_46_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_46_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_46_sync).
 - exact ran.
Qed.
Lemma global_leaf_47_sync : node_sync_check generated_modules multiplier_instances [::] 289=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_47_register : flat_register_certificate 289 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_47_preserved invalid snapshot final value
 (known:circuit_lookup [::] 289 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 289 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_47_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_47_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_47_sync).
 - exact ran.
Qed.
Lemma global_leaf_48_sync : node_sync_check generated_modules multiplier_instances [::] 291=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_48_register : flat_register_certificate 291 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_48_preserved invalid snapshot final value
 (known:circuit_lookup [::] 291 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 291 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_48_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_48_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_48_sync).
 - exact ran.
Qed.
Lemma global_leaf_49_sync : node_sync_check generated_modules multiplier_instances [::] 293=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_49_register : flat_register_certificate 293 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_49_preserved invalid snapshot final value
 (known:circuit_lookup [::] 293 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 293 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_49_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_49_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_49_sync).
 - exact ran.
Qed.
Lemma global_leaf_50_sync : node_sync_check generated_modules multiplier_instances [::] 295=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_50_register : flat_register_certificate 295 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_50_preserved invalid snapshot final value
 (known:circuit_lookup [::] 295 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 295 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_50_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_50_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_50_sync).
 - exact ran.
Qed.
Lemma global_leaf_51_sync : node_sync_check generated_modules multiplier_instances [::] 297=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_51_register : flat_register_certificate 297 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_51_preserved invalid snapshot final value
 (known:circuit_lookup [::] 297 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 297 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_51_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_51_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_51_sync).
 - exact ran.
Qed.
Lemma global_leaf_52_sync : node_sync_check generated_modules multiplier_instances [::] 299=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_52_register : flat_register_certificate 299 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_52_preserved invalid snapshot final value
 (known:circuit_lookup [::] 299 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 299 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_52_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_52_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_52_sync).
 - exact ran.
Qed.
Lemma global_leaf_53_sync : node_sync_check generated_modules multiplier_instances [::] 3=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_53_preserved invalid snapshot final value
 (known:circuit_lookup [::] 3 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 8))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 3 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_preserves_ground with (stmts:=generated_module_3_stmts_0); [vm_compute;reflexivity|vm_compute;reflexivity|exact typed|exact known|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_53_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_53_sync).
 - exact ran.
Qed.
Lemma global_leaf_54_sync : node_sync_check generated_modules multiplier_instances [::] 301=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_54_register : flat_register_certificate 301 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_54_preserved invalid snapshot final value
 (known:circuit_lookup [::] 301 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 301 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_54_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_54_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_54_sync).
 - exact ran.
Qed.
Lemma global_leaf_55_sync : node_sync_check generated_modules multiplier_instances [::] 303=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_55_register : flat_register_certificate 303 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_55_preserved invalid snapshot final value
 (known:circuit_lookup [::] 303 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 303 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_55_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_55_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_55_sync).
 - exact ran.
Qed.
Lemma global_leaf_56_sync : node_sync_check generated_modules multiplier_instances [::] 4=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_56_preserved invalid snapshot final value
 (known:circuit_lookup [::] 4 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 4 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_preserves_ground with (stmts:=generated_module_3_stmts_0); [vm_compute;reflexivity|vm_compute;reflexivity|exact typed|exact known|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_56_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_56_sync).
 - exact ran.
Qed.
Lemma global_leaf_57_sync : node_sync_check generated_modules multiplier_instances [::] 408=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_57_register : flat_register_certificate 408 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_57_preserved invalid snapshot final value
 (known:circuit_lookup [::] 408 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 16))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 408 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_57_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_57_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_57_sync).
 - exact ran.
Qed.
Lemma global_leaf_58_sync : node_sync_check generated_modules multiplier_instances [::] 410=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_58_register : flat_register_certificate 410 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_58_preserved invalid snapshot final value
 (known:circuit_lookup [::] 410 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 410 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_58_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_58_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_58_sync).
 - exact ran.
Qed.
Lemma global_leaf_59_sync : node_sync_check generated_modules multiplier_instances [::] 416=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_59_register : flat_register_certificate 416 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_59_preserved invalid snapshot final value
 (known:circuit_lookup [::] 416 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 16))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 416 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_59_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_59_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_59_sync).
 - exact ran.
Qed.
Lemma global_leaf_60_sync : node_sync_check generated_modules multiplier_instances [::] 419=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_60_register : flat_register_certificate 419 generated_module_3_stmts_0.
Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.
Lemma global_leaf_60_preserved invalid snapshot final value
 (known:circuit_lookup [::] 419 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 419 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_register_preserved; [exact known|exact global_leaf_60_register|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_60_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_60_sync).
 - exact ran.
Qed.
Lemma global_leaf_61_sync : node_sync_check generated_modules multiplier_instances [::] 5=true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_leaf_61_preserved invalid snapshot final value
 (known:circuit_lookup [::] 5 snapshot=Some value)
 (typed:type_of_val value=Gtyp (Fuint 1))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 5 final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.
   eapply pass_preserves_ground with (stmts:=generated_module_3_stmts_0); [vm_compute;reflexivity|vm_compute;reflexivity|exact typed|exact known|exact step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_61_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_61_sync).
 - exact ran.
Qed.
