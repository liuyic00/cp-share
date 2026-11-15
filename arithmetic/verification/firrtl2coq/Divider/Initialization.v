From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import InitialMapFacts RankConvergence.
From Divider Require Import Model Stable Frames Certificates SingleModule NodeProgress.
Local Open Scope N_scope.
Lemma initial_register_13 : initial_register_certificate 13 generated_module_0_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_18 : initial_register_certificate 18 generated_module_0_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_20 : initial_register_certificate 20 generated_module_0_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_33 : initial_register_certificate 33 generated_module_0_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_38 : initial_register_certificate 38 generated_module_0_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_40 : initial_register_certificate 40 generated_module_0_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_43 : initial_register_certificate 43 generated_module_0_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_45 : initial_register_certificate 45 generated_module_0_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_46 : initial_register_certificate 46 generated_module_0_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_47 : initial_register_certificate 47 generated_module_0_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_51 : initial_register_certificate 51 generated_module_0_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_445 : initial_register_certificate 445 generated_module_0_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_446 : initial_register_certificate 446 generated_module_0_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_447 : initial_register_certificate 447 generated_module_0_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_475 : initial_register_certificate 475 generated_module_0_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_476 : initial_register_certificate 476 generated_module_0_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_output_2_frame : initial_sequence_frames 2 generated_module_0_stmts_0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma initial_output_8_frame : initial_sequence_frames 8 generated_module_0_stmts_0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma initial_output_9_frame : initial_sequence_frames 9 generated_module_0_stmts_0 = true.
Proof. vm_compute. reflexivity. Qed.
Definition divider_register_values v (env : VM.t hvalue) := forall id, List.In id [:: 13; 18; 20; 33; 38; 40; 43; 45; 46; 47; 51; 445; 446; 447; 475; 476] -> VM.find id env = VM.find id (stable_env v).
Definition divider_input_values v (env : VM.t hvalue) := forall id, List.In id [:: 0; 1; 3; 4; 5; 6; 7; 10; 11; 12] -> VM.find id env = VM.find id (stable_env v).
Definition divider_externalized v (declared : VM.t hvalue) := (VM.add 12 (Gval (Fuint 1) (word_12 v)) (VM.add 11 (Gval (Fuint 1) (word_11 v)) (VM.add 10 (Gval (Fuint 1) (word_10 v)) (VM.add 7 (Gval (Fuint 1) (word_7 v)) (VM.add 6 (Gval (Fuint 64) (word_6 v)) (VM.add 5 (Gval (Fuint 64) (word_5 v)) (VM.add 4 (Gval (Fuint 64) (word_4 v)) (VM.add 3 (Gval (Fuint 1) (word_3 v)) (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.add 0 (Gval Fclock (word_0 v)) declared)))))))))).
Lemma divider_external_update v declared external
 (values : divider_input_values v external) :
 update_external_ports declared external divider_ports = Some (divider_externalized v declared).
Proof.
 have E0 : VM.find 0 external = Some (Gval Fclock (word_0 v)).
 { rewrite -(target_0_value v). apply values. simpl; tauto. }
 have E1 : VM.find 1 external = Some (Gval (Fuint 1) (word_1 v)).
 { rewrite -(target_1_value v). apply values. simpl; tauto. }
 have E3 : VM.find 3 external = Some (Gval (Fuint 1) (word_3 v)).
 { rewrite -(target_3_value v). apply values. simpl; tauto. }
 have E4 : VM.find 4 external = Some (Gval (Fuint 64) (word_4 v)).
 { rewrite -(target_4_value v). apply values. simpl; tauto. }
 have E5 : VM.find 5 external = Some (Gval (Fuint 64) (word_5 v)).
 { rewrite -(target_5_value v). apply values. simpl; tauto. }
 have E6 : VM.find 6 external = Some (Gval (Fuint 64) (word_6 v)).
 { rewrite -(target_6_value v). apply values. simpl; tauto. }
 have E7 : VM.find 7 external = Some (Gval (Fuint 1) (word_7 v)).
 { rewrite -(target_7_value v). apply values. simpl; tauto. }
 have E10 : VM.find 10 external = Some (Gval (Fuint 1) (word_10 v)).
 { rewrite -(target_10_value v). apply values. simpl; tauto. }
 have E11 : VM.find 11 external = Some (Gval (Fuint 1) (word_11 v)).
 { rewrite -(target_11_value v). apply values. simpl; tauto. }
 have E12 : VM.find 12 external = Some (Gval (Fuint 1) (word_12 v)).
 { rewrite -(target_12_value v). apply values. simpl; tauto. }
 cbn [divider_ports generated_module_0 update_external_ports is_passive].
 rewrite E0 E1 E3 E4 E5 E6 E7 E10 E11 E12. reflexivity.
Qed.
Lemma externalized_0 v declared : VM.find 0 (divider_externalized v declared) = VM.find 0 (stable_env v).
Proof. rewrite (target_0_value v). unfold divider_externalized.
 repeat first [rewrite VM.Lemmas.find_add_eq; [reflexivity|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|vm_compute; discriminate]].
Qed.
Lemma externalized_1 v declared : VM.find 1 (divider_externalized v declared) = VM.find 1 (stable_env v).
Proof. rewrite (target_1_value v). unfold divider_externalized.
 repeat first [rewrite VM.Lemmas.find_add_eq; [reflexivity|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|vm_compute; discriminate]].
Qed.
Lemma externalized_3 v declared : VM.find 3 (divider_externalized v declared) = VM.find 3 (stable_env v).
Proof. rewrite (target_3_value v). unfold divider_externalized.
 repeat first [rewrite VM.Lemmas.find_add_eq; [reflexivity|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|vm_compute; discriminate]].
Qed.
Lemma externalized_4 v declared : VM.find 4 (divider_externalized v declared) = VM.find 4 (stable_env v).
Proof. rewrite (target_4_value v). unfold divider_externalized.
 repeat first [rewrite VM.Lemmas.find_add_eq; [reflexivity|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|vm_compute; discriminate]].
Qed.
Lemma externalized_5 v declared : VM.find 5 (divider_externalized v declared) = VM.find 5 (stable_env v).
Proof. rewrite (target_5_value v). unfold divider_externalized.
 repeat first [rewrite VM.Lemmas.find_add_eq; [reflexivity|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|vm_compute; discriminate]].
Qed.
Lemma externalized_6 v declared : VM.find 6 (divider_externalized v declared) = VM.find 6 (stable_env v).
Proof. rewrite (target_6_value v). unfold divider_externalized.
 repeat first [rewrite VM.Lemmas.find_add_eq; [reflexivity|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|vm_compute; discriminate]].
Qed.
Lemma externalized_7 v declared : VM.find 7 (divider_externalized v declared) = VM.find 7 (stable_env v).
Proof. rewrite (target_7_value v). unfold divider_externalized.
 repeat first [rewrite VM.Lemmas.find_add_eq; [reflexivity|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|vm_compute; discriminate]].
Qed.
Lemma externalized_10 v declared : VM.find 10 (divider_externalized v declared) = VM.find 10 (stable_env v).
Proof. rewrite (target_10_value v). unfold divider_externalized.
 repeat first [rewrite VM.Lemmas.find_add_eq; [reflexivity|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|vm_compute; discriminate]].
Qed.
Lemma externalized_11 v declared : VM.find 11 (divider_externalized v declared) = VM.find 11 (stable_env v).
Proof. rewrite (target_11_value v). unfold divider_externalized.
 repeat first [rewrite VM.Lemmas.find_add_eq; [reflexivity|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|vm_compute; discriminate]].
Qed.
Lemma externalized_12 v declared : VM.find 12 (divider_externalized v declared) = VM.find 12 (stable_env v).
Proof. rewrite (target_12_value v). unfold divider_externalized.
 repeat first [rewrite VM.Lemmas.find_add_eq; [reflexivity|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|vm_compute; discriminate]].
Qed.
Lemma externalized_13 v declared : VM.find 13 (divider_externalized v declared) = VM.find 13 declared.
Proof. unfold divider_externalized.
 repeat (rewrite VM.Lemmas.find_add_neq; [|vm_compute; discriminate]). reflexivity.
Qed.
Lemma externalized_18 v declared : VM.find 18 (divider_externalized v declared) = VM.find 18 declared.
Proof. unfold divider_externalized.
 repeat (rewrite VM.Lemmas.find_add_neq; [|vm_compute; discriminate]). reflexivity.
Qed.
Lemma externalized_20 v declared : VM.find 20 (divider_externalized v declared) = VM.find 20 declared.
Proof. unfold divider_externalized.
 repeat (rewrite VM.Lemmas.find_add_neq; [|vm_compute; discriminate]). reflexivity.
Qed.
Lemma externalized_33 v declared : VM.find 33 (divider_externalized v declared) = VM.find 33 declared.
Proof. unfold divider_externalized.
 repeat (rewrite VM.Lemmas.find_add_neq; [|vm_compute; discriminate]). reflexivity.
Qed.
Lemma externalized_38 v declared : VM.find 38 (divider_externalized v declared) = VM.find 38 declared.
Proof. unfold divider_externalized.
 repeat (rewrite VM.Lemmas.find_add_neq; [|vm_compute; discriminate]). reflexivity.
Qed.
Lemma externalized_40 v declared : VM.find 40 (divider_externalized v declared) = VM.find 40 declared.
Proof. unfold divider_externalized.
 repeat (rewrite VM.Lemmas.find_add_neq; [|vm_compute; discriminate]). reflexivity.
Qed.
Lemma externalized_43 v declared : VM.find 43 (divider_externalized v declared) = VM.find 43 declared.
Proof. unfold divider_externalized.
 repeat (rewrite VM.Lemmas.find_add_neq; [|vm_compute; discriminate]). reflexivity.
Qed.
Lemma externalized_45 v declared : VM.find 45 (divider_externalized v declared) = VM.find 45 declared.
Proof. unfold divider_externalized.
 repeat (rewrite VM.Lemmas.find_add_neq; [|vm_compute; discriminate]). reflexivity.
Qed.
Lemma externalized_46 v declared : VM.find 46 (divider_externalized v declared) = VM.find 46 declared.
Proof. unfold divider_externalized.
 repeat (rewrite VM.Lemmas.find_add_neq; [|vm_compute; discriminate]). reflexivity.
Qed.
Lemma externalized_47 v declared : VM.find 47 (divider_externalized v declared) = VM.find 47 declared.
Proof. unfold divider_externalized.
 repeat (rewrite VM.Lemmas.find_add_neq; [|vm_compute; discriminate]). reflexivity.
Qed.
Lemma externalized_51 v declared : VM.find 51 (divider_externalized v declared) = VM.find 51 declared.
Proof. unfold divider_externalized.
 repeat (rewrite VM.Lemmas.find_add_neq; [|vm_compute; discriminate]). reflexivity.
Qed.
Lemma externalized_445 v declared : VM.find 445 (divider_externalized v declared) = VM.find 445 declared.
Proof. unfold divider_externalized.
 repeat (rewrite VM.Lemmas.find_add_neq; [|vm_compute; discriminate]). reflexivity.
Qed.
Lemma externalized_446 v declared : VM.find 446 (divider_externalized v declared) = VM.find 446 declared.
Proof. unfold divider_externalized.
 repeat (rewrite VM.Lemmas.find_add_neq; [|vm_compute; discriminate]). reflexivity.
Qed.
Lemma externalized_447 v declared : VM.find 447 (divider_externalized v declared) = VM.find 447 declared.
Proof. unfold divider_externalized.
 repeat (rewrite VM.Lemmas.find_add_neq; [|vm_compute; discriminate]). reflexivity.
Qed.
Lemma externalized_475 v declared : VM.find 475 (divider_externalized v declared) = VM.find 475 declared.
Proof. unfold divider_externalized.
 repeat (rewrite VM.Lemmas.find_add_neq; [|vm_compute; discriminate]). reflexivity.
Qed.
Lemma externalized_476 v declared : VM.find 476 (divider_externalized v declared) = VM.find 476 declared.
Proof. unfold divider_externalized.
 repeat (rewrite VM.Lemmas.find_add_neq; [|vm_compute; discriminate]). reflexivity.
Qed.
Lemma externalized_2 v declared : VM.find 2 (divider_externalized v declared) = VM.find 2 declared.
Proof. unfold divider_externalized.
 repeat (rewrite VM.Lemmas.find_add_neq; [|vm_compute; discriminate]). reflexivity.
Qed.
Lemma externalized_8 v declared : VM.find 8 (divider_externalized v declared) = VM.find 8 declared.
Proof. unfold divider_externalized.
 repeat (rewrite VM.Lemmas.find_add_neq; [|vm_compute; discriminate]). reflexivity.
Qed.
Lemma externalized_9 v declared : VM.find 9 (divider_externalized v declared) = VM.find 9 declared.
Proof. unfold divider_externalized.
 repeat (rewrite VM.Lemmas.find_add_neq; [|vm_compute; discriminate]). reflexivity.
Qed.
Lemma divider_initial_ranked v previous old external states
 (old_found : SVM.find [::] previous = Some old)
 (registers : divider_register_values v old)
 (inputs : divider_input_values v external)
 (ran : circuit_initial_map_with_memory generated_modules generated_top (Some previous) external = Some states) :
 exists env, SVM.find [::] states = Some env /\ divider_ranked v O env.
Proof.
 destruct (divider_initial_local _ _ _ ran) as [declared [env [Declared [External Found]]]].
 change (statements_initial_map_with_memory generated_modules generated_module_0_stmts_0 (SVM.find [::] previous) (ports_initial_map divider_ports) = Some declared) in Declared. rewrite old_found in Declared.
 rewrite (divider_external_update v declared external inputs) in External. inversion External; subst env.
 exists (divider_externalized v declared). split; [exact Found|].
 have L0 := externalized_0 v declared.
 have L1 := externalized_1 v declared.
 have L3 := externalized_3 v declared.
 have L4 := externalized_4 v declared.
 have L5 := externalized_5 v declared.
 have L6 := externalized_6 v declared.
 have L7 := externalized_7 v declared.
 have L10 := externalized_10 v declared.
 have L11 := externalized_11 v declared.
 have L12 := externalized_12 v declared.
 have L13 : VM.find 13 (divider_externalized v declared) = VM.find 13 (stable_env v).
 { rewrite externalized_13 (target_13_value v).
    eapply initial_register_value; [|exact initial_register_13|exact Declared].
    rewrite -(target_13_value v). apply registers. simpl; tauto. }
 have L18 : VM.find 18 (divider_externalized v declared) = VM.find 18 (stable_env v).
 { rewrite externalized_18 (target_18_value v).
    eapply initial_register_value; [|exact initial_register_18|exact Declared].
    rewrite -(target_18_value v). apply registers. simpl; tauto. }
 have L20 : VM.find 20 (divider_externalized v declared) = VM.find 20 (stable_env v).
 { rewrite externalized_20 (target_20_value v).
    eapply initial_register_value; [|exact initial_register_20|exact Declared].
    rewrite -(target_20_value v). apply registers. simpl; tauto. }
 have L33 : VM.find 33 (divider_externalized v declared) = VM.find 33 (stable_env v).
 { rewrite externalized_33 (target_33_value v).
    eapply initial_register_value; [|exact initial_register_33|exact Declared].
    rewrite -(target_33_value v). apply registers. simpl; tauto. }
 have L38 : VM.find 38 (divider_externalized v declared) = VM.find 38 (stable_env v).
 { rewrite externalized_38 (target_38_value v).
    eapply initial_register_value; [|exact initial_register_38|exact Declared].
    rewrite -(target_38_value v). apply registers. simpl; tauto. }
 have L40 : VM.find 40 (divider_externalized v declared) = VM.find 40 (stable_env v).
 { rewrite externalized_40 (target_40_value v).
    eapply initial_register_value; [|exact initial_register_40|exact Declared].
    rewrite -(target_40_value v). apply registers. simpl; tauto. }
 have L43 : VM.find 43 (divider_externalized v declared) = VM.find 43 (stable_env v).
 { rewrite externalized_43 (target_43_value v).
    eapply initial_register_value; [|exact initial_register_43|exact Declared].
    rewrite -(target_43_value v). apply registers. simpl; tauto. }
 have L45 : VM.find 45 (divider_externalized v declared) = VM.find 45 (stable_env v).
 { rewrite externalized_45 (target_45_value v).
    eapply initial_register_value; [|exact initial_register_45|exact Declared].
    rewrite -(target_45_value v). apply registers. simpl; tauto. }
 have L46 : VM.find 46 (divider_externalized v declared) = VM.find 46 (stable_env v).
 { rewrite externalized_46 (target_46_value v).
    eapply initial_register_value; [|exact initial_register_46|exact Declared].
    rewrite -(target_46_value v). apply registers. simpl; tauto. }
 have L47 : VM.find 47 (divider_externalized v declared) = VM.find 47 (stable_env v).
 { rewrite externalized_47 (target_47_value v).
    eapply initial_register_value; [|exact initial_register_47|exact Declared].
    rewrite -(target_47_value v). apply registers. simpl; tauto. }
 have L51 : VM.find 51 (divider_externalized v declared) = VM.find 51 (stable_env v).
 { rewrite externalized_51 (target_51_value v).
    eapply initial_register_value; [|exact initial_register_51|exact Declared].
    rewrite -(target_51_value v). apply registers. simpl; tauto. }
 have L445 : VM.find 445 (divider_externalized v declared) = VM.find 445 (stable_env v).
 { rewrite externalized_445 (target_445_value v).
    eapply initial_register_value; [|exact initial_register_445|exact Declared].
    rewrite -(target_445_value v). apply registers. simpl; tauto. }
 have L446 : VM.find 446 (divider_externalized v declared) = VM.find 446 (stable_env v).
 { rewrite externalized_446 (target_446_value v).
    eapply initial_register_value; [|exact initial_register_446|exact Declared].
    rewrite -(target_446_value v). apply registers. simpl; tauto. }
 have L447 : VM.find 447 (divider_externalized v declared) = VM.find 447 (stable_env v).
 { rewrite externalized_447 (target_447_value v).
    eapply initial_register_value; [|exact initial_register_447|exact Declared].
    rewrite -(target_447_value v). apply registers. simpl; tauto. }
 have L475 : VM.find 475 (divider_externalized v declared) = VM.find 475 (stable_env v).
 { rewrite externalized_475 (target_475_value v).
    eapply initial_register_value; [|exact initial_register_475|exact Declared].
    rewrite -(target_475_value v). apply registers. simpl; tauto. }
 have L476 : VM.find 476 (divider_externalized v declared) = VM.find 476 (stable_env v).
 { rewrite externalized_476 (target_476_value v).
    eapply initial_register_value; [|exact initial_register_476|exact Declared].
    rewrite -(target_476_value v). apply registers. simpl; tauto. }
 have T2 : VM.find 2 (divider_externalized v declared) = Some (Needtobedefined (Gtyp (Fuint 1))).
 { rewrite externalized_2 (initial_sequence_preserves _ _ _ _ _ _ initial_output_2_frame Declared). reflexivity. }
 have T8 : VM.find 8 (divider_externalized v declared) = Some (Needtobedefined (Gtyp (Fuint 1))).
 { rewrite externalized_8 (initial_sequence_preserves _ _ _ _ _ _ initial_output_8_frame Declared). reflexivity. }
 have T9 : VM.find 9 (divider_externalized v declared) = Some (Needtobedefined (Gtyp (Fuint 64))).
 { rewrite externalized_9 (initial_sequence_preserves _ _ _ _ _ _ initial_output_9_frame Declared). reflexivity. }
 split.
 - intros id inside bound. apply divider_domain_cases in inside. unfold divider_ids in inside.
   repeat destruct inside as [same|inside]; try contradiction; subst id; cbn [dependency_rank] in bound; try lia; assumption.
 - split; [exists (Needtobedefined (Gtyp (Fuint 1))); split; [exact T2|reflexivity]|].
   split; [exists (Needtobedefined (Gtyp (Fuint 1))); split; [exact T8|reflexivity]|].
   exists (Needtobedefined (Gtyp (Fuint 64))); split; [exact T9|reflexivity].
Qed.
Print Assumptions divider_initial_ranked.
