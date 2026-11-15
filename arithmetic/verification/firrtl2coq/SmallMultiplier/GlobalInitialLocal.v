From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import InitialMapFacts InitialInstanceFacts CircuitInitialFacts HierarchyFacts PortFieldFacts.
From SmallMultiplier Require Import Model GlobalStable GlobalInstances GlobalProgressTypes.
Local Open Scope N_scope.
Lemma initial_output_0_4 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_0_stmts_0 previous (ports_initial_map(multiplier_ports 0))=Some env) :
 VM.find 4 env=Some(Needtobedefined(Gtyp(Fuint 1))).
Proof.
 rewrite (initial_sequence_preserves generated_modules previous 4 generated_module_0_stmts_0 (ports_initial_map(multiplier_ports 0)) env (ltac:(vm_compute;reflexivity)) ran).
 reflexivity.
Qed.
Lemma initial_output_0_5 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_0_stmts_0 previous (ports_initial_map(multiplier_ports 0))=Some env) :
 VM.find 5 env=Some(Needtobedefined(Gtyp(Fuint 1))).
Proof.
 rewrite (initial_sequence_preserves generated_modules previous 5 generated_module_0_stmts_0 (ports_initial_map(multiplier_ports 0)) env (ltac:(vm_compute;reflexivity)) ran).
 reflexivity.
Qed.
Lemma initial_output_1_5 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_1_stmts_0 previous (ports_initial_map(multiplier_ports 1))=Some env) :
 VM.find 5 env=Some(Needtobedefined(Gtyp(Fuint 1))).
Proof.
 rewrite (initial_sequence_preserves generated_modules previous 5 generated_module_1_stmts_0 (ports_initial_map(multiplier_ports 1)) env (ltac:(vm_compute;reflexivity)) ran).
 reflexivity.
Qed.
Lemma initial_output_1_6 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_1_stmts_0 previous (ports_initial_map(multiplier_ports 1))=Some env) :
 VM.find 6 env=Some(Needtobedefined(Gtyp(Fuint 1))).
Proof.
 rewrite (initial_sequence_preserves generated_modules previous 6 generated_module_1_stmts_0 (ports_initial_map(multiplier_ports 1)) env (ltac:(vm_compute;reflexivity)) ran).
 reflexivity.
Qed.
Lemma initial_output_2_7 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_2_stmts_0 previous (ports_initial_map(multiplier_ports 2))=Some env) :
 VM.find 7 env=Some(Needtobedefined(Gtyp(Fuint 1))).
Proof.
 rewrite (initial_sequence_preserves generated_modules previous 7 generated_module_2_stmts_0 (ports_initial_map(multiplier_ports 2)) env (ltac:(vm_compute;reflexivity)) ran).
 reflexivity.
Qed.
Lemma initial_output_2_8 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_2_stmts_0 previous (ports_initial_map(multiplier_ports 2))=Some env) :
 VM.find 8 env=Some(Needtobedefined(Gtyp(Fuint 1))).
Proof.
 rewrite (initial_sequence_preserves generated_modules previous 8 generated_module_2_stmts_0 (ports_initial_map(multiplier_ports 2)) env (ltac:(vm_compute;reflexivity)) ran).
 reflexivity.
Qed.
Lemma initial_output_2_9 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_2_stmts_0 previous (ports_initial_map(multiplier_ports 2))=Some env) :
 VM.find 9 env=Some(Needtobedefined(Gtyp(Fuint 1))).
Proof.
 rewrite (initial_sequence_preserves generated_modules previous 9 generated_module_2_stmts_0 (ports_initial_map(multiplier_ports 2)) env (ltac:(vm_compute;reflexivity)) ran).
 reflexivity.
Qed.
Lemma initial_instance_2_10 : initial_instance_certificate 10 1 generated_module_2_stmts_0.
Proof. apply checked_initial_instance_sound. vm_compute. reflexivity. Qed.
Definition instance_type_2_10 := Eval vm_compute in match module_type generated_modules 1 with Some t=>t|None=>Gtyp(Fuint 0)end.
Lemma initial_bundle_2_10 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_2_stmts_0 previous (ports_initial_map(multiplier_ports 2))=Some env) :
 VM.find 10 env=Some(Needtobedefined instance_type_2_10).
Proof. eapply (initial_instance_value generated_modules previous 10 1 instance_type_2_10 generated_module_2_stmts_0); [reflexivity|exact initial_instance_2_10|exact ran]. Qed.
Lemma initial_instance_2_11 : initial_instance_certificate 11 1 generated_module_2_stmts_0.
Proof. apply checked_initial_instance_sound. vm_compute. reflexivity. Qed.
Definition instance_type_2_11 := Eval vm_compute in match module_type generated_modules 1 with Some t=>t|None=>Gtyp(Fuint 0)end.
Lemma initial_bundle_2_11 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_2_stmts_0 previous (ports_initial_map(multiplier_ports 2))=Some env) :
 VM.find 11 env=Some(Needtobedefined instance_type_2_11).
Proof. eapply (initial_instance_value generated_modules previous 11 1 instance_type_2_11 generated_module_2_stmts_0); [reflexivity|exact initial_instance_2_11|exact ran]. Qed.
Lemma initial_output_3_6 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_3_stmts_0 previous (ports_initial_map(multiplier_ports 3))=Some env) :
 VM.find 6 env=Some(Needtobedefined(Gtyp(Fuint 16))).
Proof.
 rewrite (initial_sequence_preserves generated_modules previous 6 generated_module_3_stmts_0 (ports_initial_map(multiplier_ports 3)) env (ltac:(vm_compute;reflexivity)) ran).
 reflexivity.
Qed.
Lemma initial_instance_3_7 : initial_instance_certificate 7 0 generated_module_3_stmts_0.
Proof. apply checked_initial_instance_sound. vm_compute. reflexivity. Qed.
Definition instance_type_3_7 := Eval vm_compute in match module_type generated_modules 0 with Some t=>t|None=>Gtyp(Fuint 0)end.
Lemma initial_bundle_3_7 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_3_stmts_0 previous (ports_initial_map(multiplier_ports 3))=Some env) :
 VM.find 7 env=Some(Needtobedefined instance_type_3_7).
Proof. eapply (initial_instance_value generated_modules previous 7 0 instance_type_3_7 generated_module_3_stmts_0); [reflexivity|exact initial_instance_3_7|exact ran]. Qed.
Lemma initial_instance_3_8 : initial_instance_certificate 8 0 generated_module_3_stmts_0.
Proof. apply checked_initial_instance_sound. vm_compute. reflexivity. Qed.
Definition instance_type_3_8 := Eval vm_compute in match module_type generated_modules 0 with Some t=>t|None=>Gtyp(Fuint 0)end.
Lemma initial_bundle_3_8 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_3_stmts_0 previous (ports_initial_map(multiplier_ports 3))=Some env) :
 VM.find 8 env=Some(Needtobedefined instance_type_3_8).
Proof. eapply (initial_instance_value generated_modules previous 8 0 instance_type_3_8 generated_module_3_stmts_0); [reflexivity|exact initial_instance_3_8|exact ran]. Qed.
Lemma initial_instance_3_9 : initial_instance_certificate 9 1 generated_module_3_stmts_0.
Proof. apply checked_initial_instance_sound. vm_compute. reflexivity. Qed.
Definition instance_type_3_9 := Eval vm_compute in match module_type generated_modules 1 with Some t=>t|None=>Gtyp(Fuint 0)end.
Lemma initial_bundle_3_9 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_3_stmts_0 previous (ports_initial_map(multiplier_ports 3))=Some env) :
 VM.find 9 env=Some(Needtobedefined instance_type_3_9).
Proof. eapply (initial_instance_value generated_modules previous 9 1 instance_type_3_9 generated_module_3_stmts_0); [reflexivity|exact initial_instance_3_9|exact ran]. Qed.
Lemma initial_instance_3_10 : initial_instance_certificate 10 1 generated_module_3_stmts_0.
Proof. apply checked_initial_instance_sound. vm_compute. reflexivity. Qed.
Definition instance_type_3_10 := Eval vm_compute in match module_type generated_modules 1 with Some t=>t|None=>Gtyp(Fuint 0)end.
Lemma initial_bundle_3_10 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_3_stmts_0 previous (ports_initial_map(multiplier_ports 3))=Some env) :
 VM.find 10 env=Some(Needtobedefined instance_type_3_10).
Proof. eapply (initial_instance_value generated_modules previous 10 1 instance_type_3_10 generated_module_3_stmts_0); [reflexivity|exact initial_instance_3_10|exact ran]. Qed.
Lemma initial_instance_3_11 : initial_instance_certificate 11 2 generated_module_3_stmts_0.
Proof. apply checked_initial_instance_sound. vm_compute. reflexivity. Qed.
Definition instance_type_3_11 := Eval vm_compute in match module_type generated_modules 2 with Some t=>t|None=>Gtyp(Fuint 0)end.
Lemma initial_bundle_3_11 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_3_stmts_0 previous (ports_initial_map(multiplier_ports 3))=Some env) :
 VM.find 11 env=Some(Needtobedefined instance_type_3_11).
Proof. eapply (initial_instance_value generated_modules previous 11 2 instance_type_3_11 generated_module_3_stmts_0); [reflexivity|exact initial_instance_3_11|exact ran]. Qed.
Lemma initial_instance_3_12 : initial_instance_certificate 12 2 generated_module_3_stmts_0.
Proof. apply checked_initial_instance_sound. vm_compute. reflexivity. Qed.
Definition instance_type_3_12 := Eval vm_compute in match module_type generated_modules 2 with Some t=>t|None=>Gtyp(Fuint 0)end.
Lemma initial_bundle_3_12 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_3_stmts_0 previous (ports_initial_map(multiplier_ports 3))=Some env) :
 VM.find 12 env=Some(Needtobedefined instance_type_3_12).
Proof. eapply (initial_instance_value generated_modules previous 12 2 instance_type_3_12 generated_module_3_stmts_0); [reflexivity|exact initial_instance_3_12|exact ran]. Qed.
Lemma initial_instance_3_13 : initial_instance_certificate 13 2 generated_module_3_stmts_0.
Proof. apply checked_initial_instance_sound. vm_compute. reflexivity. Qed.
Definition instance_type_3_13 := Eval vm_compute in match module_type generated_modules 2 with Some t=>t|None=>Gtyp(Fuint 0)end.
Lemma initial_bundle_3_13 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_3_stmts_0 previous (ports_initial_map(multiplier_ports 3))=Some env) :
 VM.find 13 env=Some(Needtobedefined instance_type_3_13).
Proof. eapply (initial_instance_value generated_modules previous 13 2 instance_type_3_13 generated_module_3_stmts_0); [reflexivity|exact initial_instance_3_13|exact ran]. Qed.
Lemma initial_instance_3_14 : initial_instance_certificate 14 2 generated_module_3_stmts_0.
Proof. apply checked_initial_instance_sound. vm_compute. reflexivity. Qed.
Definition instance_type_3_14 := Eval vm_compute in match module_type generated_modules 2 with Some t=>t|None=>Gtyp(Fuint 0)end.
Lemma initial_bundle_3_14 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_3_stmts_0 previous (ports_initial_map(multiplier_ports 3))=Some env) :
 VM.find 14 env=Some(Needtobedefined instance_type_3_14).
Proof. eapply (initial_instance_value generated_modules previous 14 2 instance_type_3_14 generated_module_3_stmts_0); [reflexivity|exact initial_instance_3_14|exact ran]. Qed.
Lemma initial_instance_3_15 : initial_instance_certificate 15 2 generated_module_3_stmts_0.
Proof. apply checked_initial_instance_sound. vm_compute. reflexivity. Qed.
Definition instance_type_3_15 := Eval vm_compute in match module_type generated_modules 2 with Some t=>t|None=>Gtyp(Fuint 0)end.
Lemma initial_bundle_3_15 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_3_stmts_0 previous (ports_initial_map(multiplier_ports 3))=Some env) :
 VM.find 15 env=Some(Needtobedefined instance_type_3_15).
Proof. eapply (initial_instance_value generated_modules previous 15 2 instance_type_3_15 generated_module_3_stmts_0); [reflexivity|exact initial_instance_3_15|exact ran]. Qed.
Lemma initial_instance_3_16 : initial_instance_certificate 16 2 generated_module_3_stmts_0.
Proof. apply checked_initial_instance_sound. vm_compute. reflexivity. Qed.
Definition instance_type_3_16 := Eval vm_compute in match module_type generated_modules 2 with Some t=>t|None=>Gtyp(Fuint 0)end.
Lemma initial_bundle_3_16 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_3_stmts_0 previous (ports_initial_map(multiplier_ports 3))=Some env) :
 VM.find 16 env=Some(Needtobedefined instance_type_3_16).
Proof. eapply (initial_instance_value generated_modules previous 16 2 instance_type_3_16 generated_module_3_stmts_0); [reflexivity|exact initial_instance_3_16|exact ran]. Qed.
Lemma initial_instance_3_17 : initial_instance_certificate 17 2 generated_module_3_stmts_0.
Proof. apply checked_initial_instance_sound. vm_compute. reflexivity. Qed.
Definition instance_type_3_17 := Eval vm_compute in match module_type generated_modules 2 with Some t=>t|None=>Gtyp(Fuint 0)end.
Lemma initial_bundle_3_17 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_3_stmts_0 previous (ports_initial_map(multiplier_ports 3))=Some env) :
 VM.find 17 env=Some(Needtobedefined instance_type_3_17).
Proof. eapply (initial_instance_value generated_modules previous 17 2 instance_type_3_17 generated_module_3_stmts_0); [reflexivity|exact initial_instance_3_17|exact ran]. Qed.
Lemma initial_instance_3_18 : initial_instance_certificate 18 2 generated_module_3_stmts_0.
Proof. apply checked_initial_instance_sound. vm_compute. reflexivity. Qed.
Definition instance_type_3_18 := Eval vm_compute in match module_type generated_modules 2 with Some t=>t|None=>Gtyp(Fuint 0)end.
Lemma initial_bundle_3_18 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_3_stmts_0 previous (ports_initial_map(multiplier_ports 3))=Some env) :
 VM.find 18 env=Some(Needtobedefined instance_type_3_18).
Proof. eapply (initial_instance_value generated_modules previous 18 2 instance_type_3_18 generated_module_3_stmts_0); [reflexivity|exact initial_instance_3_18|exact ran]. Qed.
Lemma initial_instance_3_19 : initial_instance_certificate 19 1 generated_module_3_stmts_0.
Proof. apply checked_initial_instance_sound. vm_compute. reflexivity. Qed.
Definition instance_type_3_19 := Eval vm_compute in match module_type generated_modules 1 with Some t=>t|None=>Gtyp(Fuint 0)end.
Lemma initial_bundle_3_19 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_3_stmts_0 previous (ports_initial_map(multiplier_ports 3))=Some env) :
 VM.find 19 env=Some(Needtobedefined instance_type_3_19).
Proof. eapply (initial_instance_value generated_modules previous 19 1 instance_type_3_19 generated_module_3_stmts_0); [reflexivity|exact initial_instance_3_19|exact ran]. Qed.
Lemma initial_instance_3_20 : initial_instance_certificate 20 0 generated_module_3_stmts_0.
Proof. apply checked_initial_instance_sound. vm_compute. reflexivity. Qed.
Definition instance_type_3_20 := Eval vm_compute in match module_type generated_modules 0 with Some t=>t|None=>Gtyp(Fuint 0)end.
Lemma initial_bundle_3_20 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_3_stmts_0 previous (ports_initial_map(multiplier_ports 3))=Some env) :
 VM.find 20 env=Some(Needtobedefined instance_type_3_20).
Proof. eapply (initial_instance_value generated_modules previous 20 0 instance_type_3_20 generated_module_3_stmts_0); [reflexivity|exact initial_instance_3_20|exact ran]. Qed.
Lemma initial_instance_3_21 : initial_instance_certificate 21 0 generated_module_3_stmts_0.
Proof. apply checked_initial_instance_sound. vm_compute. reflexivity. Qed.
Definition instance_type_3_21 := Eval vm_compute in match module_type generated_modules 0 with Some t=>t|None=>Gtyp(Fuint 0)end.
Lemma initial_bundle_3_21 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_3_stmts_0 previous (ports_initial_map(multiplier_ports 3))=Some env) :
 VM.find 21 env=Some(Needtobedefined instance_type_3_21).
Proof. eapply (initial_instance_value generated_modules previous 21 0 instance_type_3_21 generated_module_3_stmts_0); [reflexivity|exact initial_instance_3_21|exact ran]. Qed.
Lemma initial_instance_3_22 : initial_instance_certificate 22 0 generated_module_3_stmts_0.
Proof. apply checked_initial_instance_sound. vm_compute. reflexivity. Qed.
Definition instance_type_3_22 := Eval vm_compute in match module_type generated_modules 0 with Some t=>t|None=>Gtyp(Fuint 0)end.
Lemma initial_bundle_3_22 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_3_stmts_0 previous (ports_initial_map(multiplier_ports 3))=Some env) :
 VM.find 22 env=Some(Needtobedefined instance_type_3_22).
Proof. eapply (initial_instance_value generated_modules previous 22 0 instance_type_3_22 generated_module_3_stmts_0); [reflexivity|exact initial_instance_3_22|exact ran]. Qed.
Lemma initial_instance_3_23 : initial_instance_certificate 23 0 generated_module_3_stmts_0.
Proof. apply checked_initial_instance_sound. vm_compute. reflexivity. Qed.
Definition instance_type_3_23 := Eval vm_compute in match module_type generated_modules 0 with Some t=>t|None=>Gtyp(Fuint 0)end.
Lemma initial_bundle_3_23 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_3_stmts_0 previous (ports_initial_map(multiplier_ports 3))=Some env) :
 VM.find 23 env=Some(Needtobedefined instance_type_3_23).
Proof. eapply (initial_instance_value generated_modules previous 23 0 instance_type_3_23 generated_module_3_stmts_0); [reflexivity|exact initial_instance_3_23|exact ran]. Qed.
Lemma initial_instance_3_24 : initial_instance_certificate 24 0 generated_module_3_stmts_0.
Proof. apply checked_initial_instance_sound. vm_compute. reflexivity. Qed.
Definition instance_type_3_24 := Eval vm_compute in match module_type generated_modules 0 with Some t=>t|None=>Gtyp(Fuint 0)end.
Lemma initial_bundle_3_24 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_3_stmts_0 previous (ports_initial_map(multiplier_ports 3))=Some env) :
 VM.find 24 env=Some(Needtobedefined instance_type_3_24).
Proof. eapply (initial_instance_value generated_modules previous 24 0 instance_type_3_24 generated_module_3_stmts_0); [reflexivity|exact initial_instance_3_24|exact ran]. Qed.
Lemma initial_instance_3_25 : initial_instance_certificate 25 0 generated_module_3_stmts_0.
Proof. apply checked_initial_instance_sound. vm_compute. reflexivity. Qed.
Definition instance_type_3_25 := Eval vm_compute in match module_type generated_modules 0 with Some t=>t|None=>Gtyp(Fuint 0)end.
Lemma initial_bundle_3_25 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_3_stmts_0 previous (ports_initial_map(multiplier_ports 3))=Some env) :
 VM.find 25 env=Some(Needtobedefined instance_type_3_25).
Proof. eapply (initial_instance_value generated_modules previous 25 0 instance_type_3_25 generated_module_3_stmts_0); [reflexivity|exact initial_instance_3_25|exact ran]. Qed.
Lemma initial_instance_3_26 : initial_instance_certificate 26 0 generated_module_3_stmts_0.
Proof. apply checked_initial_instance_sound. vm_compute. reflexivity. Qed.
Definition instance_type_3_26 := Eval vm_compute in match module_type generated_modules 0 with Some t=>t|None=>Gtyp(Fuint 0)end.
Lemma initial_bundle_3_26 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_3_stmts_0 previous (ports_initial_map(multiplier_ports 3))=Some env) :
 VM.find 26 env=Some(Needtobedefined instance_type_3_26).
Proof. eapply (initial_instance_value generated_modules previous 26 0 instance_type_3_26 generated_module_3_stmts_0); [reflexivity|exact initial_instance_3_26|exact ran]. Qed.
Lemma initial_instance_3_27 : initial_instance_certificate 27 1 generated_module_3_stmts_0.
Proof. apply checked_initial_instance_sound. vm_compute. reflexivity. Qed.
Definition instance_type_3_27 := Eval vm_compute in match module_type generated_modules 1 with Some t=>t|None=>Gtyp(Fuint 0)end.
Lemma initial_bundle_3_27 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_3_stmts_0 previous (ports_initial_map(multiplier_ports 3))=Some env) :
 VM.find 27 env=Some(Needtobedefined instance_type_3_27).
Proof. eapply (initial_instance_value generated_modules previous 27 1 instance_type_3_27 generated_module_3_stmts_0); [reflexivity|exact initial_instance_3_27|exact ran]. Qed.
Lemma initial_instance_3_28 : initial_instance_certificate 28 1 generated_module_3_stmts_0.
Proof. apply checked_initial_instance_sound. vm_compute. reflexivity. Qed.
Definition instance_type_3_28 := Eval vm_compute in match module_type generated_modules 1 with Some t=>t|None=>Gtyp(Fuint 0)end.
Lemma initial_bundle_3_28 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_3_stmts_0 previous (ports_initial_map(multiplier_ports 3))=Some env) :
 VM.find 28 env=Some(Needtobedefined instance_type_3_28).
Proof. eapply (initial_instance_value generated_modules previous 28 1 instance_type_3_28 generated_module_3_stmts_0); [reflexivity|exact initial_instance_3_28|exact ran]. Qed.
Lemma initial_instance_3_29 : initial_instance_certificate 29 0 generated_module_3_stmts_0.
Proof. apply checked_initial_instance_sound. vm_compute. reflexivity. Qed.
Definition instance_type_3_29 := Eval vm_compute in match module_type generated_modules 0 with Some t=>t|None=>Gtyp(Fuint 0)end.
Lemma initial_bundle_3_29 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_3_stmts_0 previous (ports_initial_map(multiplier_ports 3))=Some env) :
 VM.find 29 env=Some(Needtobedefined instance_type_3_29).
Proof. eapply (initial_instance_value generated_modules previous 29 0 instance_type_3_29 generated_module_3_stmts_0); [reflexivity|exact initial_instance_3_29|exact ran]. Qed.
Lemma initial_instance_3_30 : initial_instance_certificate 30 0 generated_module_3_stmts_0.
Proof. apply checked_initial_instance_sound. vm_compute. reflexivity. Qed.
Definition instance_type_3_30 := Eval vm_compute in match module_type generated_modules 0 with Some t=>t|None=>Gtyp(Fuint 0)end.
Lemma initial_bundle_3_30 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_3_stmts_0 previous (ports_initial_map(multiplier_ports 3))=Some env) :
 VM.find 30 env=Some(Needtobedefined instance_type_3_30).
Proof. eapply (initial_instance_value generated_modules previous 30 0 instance_type_3_30 generated_module_3_stmts_0); [reflexivity|exact initial_instance_3_30|exact ran]. Qed.
Lemma initial_instance_3_31 : initial_instance_certificate 31 0 generated_module_3_stmts_0.
Proof. apply checked_initial_instance_sound. vm_compute. reflexivity. Qed.
Definition instance_type_3_31 := Eval vm_compute in match module_type generated_modules 0 with Some t=>t|None=>Gtyp(Fuint 0)end.
Lemma initial_bundle_3_31 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_3_stmts_0 previous (ports_initial_map(multiplier_ports 3))=Some env) :
 VM.find 31 env=Some(Needtobedefined instance_type_3_31).
Proof. eapply (initial_instance_value generated_modules previous 31 0 instance_type_3_31 generated_module_3_stmts_0); [reflexivity|exact initial_instance_3_31|exact ran]. Qed.
Lemma initial_instance_3_32 : initial_instance_certificate 32 0 generated_module_3_stmts_0.
Proof. apply checked_initial_instance_sound. vm_compute. reflexivity. Qed.
Definition instance_type_3_32 := Eval vm_compute in match module_type generated_modules 0 with Some t=>t|None=>Gtyp(Fuint 0)end.
Lemma initial_bundle_3_32 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_3_stmts_0 previous (ports_initial_map(multiplier_ports 3))=Some env) :
 VM.find 32 env=Some(Needtobedefined instance_type_3_32).
Proof. eapply (initial_instance_value generated_modules previous 32 0 instance_type_3_32 generated_module_3_stmts_0); [reflexivity|exact initial_instance_3_32|exact ran]. Qed.
Lemma initial_instance_3_33 : initial_instance_certificate 33 1 generated_module_3_stmts_0.
Proof. apply checked_initial_instance_sound. vm_compute. reflexivity. Qed.
Definition instance_type_3_33 := Eval vm_compute in match module_type generated_modules 1 with Some t=>t|None=>Gtyp(Fuint 0)end.
Lemma initial_bundle_3_33 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_3_stmts_0 previous (ports_initial_map(multiplier_ports 3))=Some env) :
 VM.find 33 env=Some(Needtobedefined instance_type_3_33).
Proof. eapply (initial_instance_value generated_modules previous 33 1 instance_type_3_33 generated_module_3_stmts_0); [reflexivity|exact initial_instance_3_33|exact ran]. Qed.
Lemma initial_instance_3_34 : initial_instance_certificate 34 0 generated_module_3_stmts_0.
Proof. apply checked_initial_instance_sound. vm_compute. reflexivity. Qed.
Definition instance_type_3_34 := Eval vm_compute in match module_type generated_modules 0 with Some t=>t|None=>Gtyp(Fuint 0)end.
Lemma initial_bundle_3_34 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_3_stmts_0 previous (ports_initial_map(multiplier_ports 3))=Some env) :
 VM.find 34 env=Some(Needtobedefined instance_type_3_34).
Proof. eapply (initial_instance_value generated_modules previous 34 0 instance_type_3_34 generated_module_3_stmts_0); [reflexivity|exact initial_instance_3_34|exact ran]. Qed.
Lemma initial_instance_3_35 : initial_instance_certificate 35 0 generated_module_3_stmts_0.
Proof. apply checked_initial_instance_sound. vm_compute. reflexivity. Qed.
Definition instance_type_3_35 := Eval vm_compute in match module_type generated_modules 0 with Some t=>t|None=>Gtyp(Fuint 0)end.
Lemma initial_bundle_3_35 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_3_stmts_0 previous (ports_initial_map(multiplier_ports 3))=Some env) :
 VM.find 35 env=Some(Needtobedefined instance_type_3_35).
Proof. eapply (initial_instance_value generated_modules previous 35 0 instance_type_3_35 generated_module_3_stmts_0); [reflexivity|exact initial_instance_3_35|exact ran]. Qed.
Lemma initial_instance_3_36 : initial_instance_certificate 36 0 generated_module_3_stmts_0.
Proof. apply checked_initial_instance_sound. vm_compute. reflexivity. Qed.
Definition instance_type_3_36 := Eval vm_compute in match module_type generated_modules 0 with Some t=>t|None=>Gtyp(Fuint 0)end.
Lemma initial_bundle_3_36 previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_3_stmts_0 previous (ports_initial_map(multiplier_ports 3))=Some env) :
 VM.find 36 env=Some(Needtobedefined instance_type_3_36).
Proof. eapply (initial_instance_value generated_modules previous 36 0 instance_type_3_36 generated_module_3_stmts_0); [reflexivity|exact initial_instance_3_36|exact ran]. Qed.
Lemma initial_register_201 : initial_register_certificate 201 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_203 : initial_register_certificate 203 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_205 : initial_register_certificate 205 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_207 : initial_register_certificate 207 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_209 : initial_register_certificate 209 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_211 : initial_register_certificate 211 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_213 : initial_register_certificate 213 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_215 : initial_register_certificate 215 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_217 : initial_register_certificate 217 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_219 : initial_register_certificate 219 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_221 : initial_register_certificate 221 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_223 : initial_register_certificate 223 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_225 : initial_register_certificate 225 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_227 : initial_register_certificate 227 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_229 : initial_register_certificate 229 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_231 : initial_register_certificate 231 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_233 : initial_register_certificate 233 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_235 : initial_register_certificate 235 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_237 : initial_register_certificate 237 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_239 : initial_register_certificate 239 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_241 : initial_register_certificate 241 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_243 : initial_register_certificate 243 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_245 : initial_register_certificate 245 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_247 : initial_register_certificate 247 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_249 : initial_register_certificate 249 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_251 : initial_register_certificate 251 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_253 : initial_register_certificate 253 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_255 : initial_register_certificate 255 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_257 : initial_register_certificate 257 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_259 : initial_register_certificate 259 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_261 : initial_register_certificate 261 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_263 : initial_register_certificate 263 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_265 : initial_register_certificate 265 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_267 : initial_register_certificate 267 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_269 : initial_register_certificate 269 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_271 : initial_register_certificate 271 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_273 : initial_register_certificate 273 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_275 : initial_register_certificate 275 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_277 : initial_register_certificate 277 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_279 : initial_register_certificate 279 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_281 : initial_register_certificate 281 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_283 : initial_register_certificate 283 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_285 : initial_register_certificate 285 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_287 : initial_register_certificate 287 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_289 : initial_register_certificate 289 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_291 : initial_register_certificate 291 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_293 : initial_register_certificate 293 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_295 : initial_register_certificate 295 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_297 : initial_register_certificate 297 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_299 : initial_register_certificate 299 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_301 : initial_register_certificate 301 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_303 : initial_register_certificate 303 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_408 : initial_register_certificate 408 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_410 : initial_register_certificate 410 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_416 : initial_register_certificate 416 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Lemma initial_register_419 : initial_register_certificate 419 generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
Definition multiplier_register_values (v:global_leaves) env := forall index, List.In index [::3%nat;4%nat;5%nat;6%nat;7%nat;8%nat;9%nat;10%nat;11%nat;12%nat;13%nat;14%nat;15%nat;16%nat;17%nat;18%nat;19%nat;20%nat;21%nat;22%nat;23%nat;24%nat;25%nat;26%nat;27%nat;28%nat;29%nat;30%nat;31%nat;32%nat;33%nat;34%nat;35%nat;36%nat;37%nat;38%nat;39%nat;40%nat;41%nat;42%nat;43%nat;44%nat;45%nat;46%nat;47%nat;48%nat;49%nat;50%nat;51%nat;52%nat;54%nat;55%nat;57%nat;58%nat;59%nat;60%nat] -> global_value_at index (SVM.add [::] env (SVM.empty(VM.t hvalue)))=Some(global_target_at index v).
Definition multiplier_input_values (v:global_leaves) external := VM.find 0 external=Some(Gval Fclock (global_word_0 v)) /\ VM.find 1 external=Some(Gval (Fuint 1) (global_word_1 v)) /\ VM.find 2 external=Some(Gval (Fuint 8) (global_word_2 v)) /\ VM.find 3 external=Some(Gval (Fuint 8) (global_word_53 v)) /\ VM.find 4 external=Some(Gval (Fuint 1) (global_word_56 v)) /\ VM.find 5 external=Some(Gval (Fuint 1) (global_word_61 v)).
Definition multiplier_externalized v env := (VM.add 5 (Gval (Fuint 1) (global_word_61 v)) (VM.add 4 (Gval (Fuint 1) (global_word_56 v)) (VM.add 3 (Gval (Fuint 8) (global_word_53 v)) (VM.add 2 (Gval (Fuint 8) (global_word_2 v)) (VM.add 1 (Gval (Fuint 1) (global_word_1 v)) (VM.add 0 (Gval Fclock (global_word_0 v)) env)))))).
Lemma multiplier_external_update v declared external (ports:multiplier_input_values v external) :
 update_external_ports declared external (multiplier_ports 3)=Some(multiplier_externalized v declared).
Proof. destruct ports as [E0 [E1 [E2 [E3 [E4 E5]]]]].
 change (update_external_ports declared external [::@Finput VarOrder.T 0 (Gtyp Fclock);@Finput VarOrder.T 1 (Gtyp(Fuint 1));@Finput VarOrder.T 2 (Gtyp(Fuint 8));@Finput VarOrder.T 3 (Gtyp(Fuint 8));@Finput VarOrder.T 4 (Gtyp(Fuint 1));@Finput VarOrder.T 5 (Gtyp(Fuint 1));@Foutput VarOrder.T 6 (Gtyp(Fuint 16))]=Some(multiplier_externalized v declared)).
 cbn [update_external_ports is_passive]. rewrite E0 E1 E2 E3 E4 E5. reflexivity.
Qed.
Lemma multiplier_external_private v env id (private:(5 < id)%num) :
 VM.find id (multiplier_externalized v env)=VM.find id env.
Proof.
 unfold multiplier_externalized.
 repeat (rewrite VM.Lemmas.find_add_neq; [|intro Same; move/eqP:Same=>Same; subst id; discriminate private]). reflexivity.
Qed.
Lemma multiplier_external_0 v env : VM.find 0 (multiplier_externalized v env)=Some(Gval Fclock (global_word_0 v)).
Proof. unfold multiplier_externalized.
 repeat first [rewrite VM.Lemmas.find_add_eq; [reflexivity|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. Qed.
Lemma multiplier_external_1 v env : VM.find 1 (multiplier_externalized v env)=Some(Gval (Fuint 1) (global_word_1 v)).
Proof. unfold multiplier_externalized.
 repeat first [rewrite VM.Lemmas.find_add_eq; [reflexivity|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. Qed.
Lemma multiplier_external_2 v env : VM.find 2 (multiplier_externalized v env)=Some(Gval (Fuint 8) (global_word_2 v)).
Proof. unfold multiplier_externalized.
 repeat first [rewrite VM.Lemmas.find_add_eq; [reflexivity|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. Qed.
Lemma multiplier_external_3 v env : VM.find 3 (multiplier_externalized v env)=Some(Gval (Fuint 8) (global_word_53 v)).
Proof. unfold multiplier_externalized.
 repeat first [rewrite VM.Lemmas.find_add_eq; [reflexivity|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. Qed.
Lemma multiplier_external_4 v env : VM.find 4 (multiplier_externalized v env)=Some(Gval (Fuint 1) (global_word_56 v)).
Proof. unfold multiplier_externalized.
 repeat first [rewrite VM.Lemmas.find_add_eq; [reflexivity|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. Qed.
Lemma multiplier_external_5 v env : VM.find 5 (multiplier_externalized v env)=Some(Gval (Fuint 1) (global_word_61 v)).
Proof. unfold multiplier_externalized.
 repeat first [rewrite VM.Lemmas.find_add_eq; [reflexivity|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. Qed.
