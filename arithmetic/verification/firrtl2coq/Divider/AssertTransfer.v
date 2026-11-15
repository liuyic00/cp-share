From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import ScalarEvaluation ScalarExtensionality.
From ArithmeticFIRRTL Require Import Radix2Divider.
From Divider Require Import Model Stable SingleModule NodeProgress.
Module Tool := ArithmeticFIRRTL.Radix2Divider.
Local Open Scope N_scope.
Lemma generated_modules_match : Tool.generated_modules = Model.generated_modules.
Proof. reflexivity. Qed.
Lemma generated_top_match : Tool.generated_top = Model.generated_top.
Proof. reflexivity. Qed.
Lemma generated_expr_transfer expr env v
 (pure : scalar_exprb expr)
 (dependencies : forall dep, List.In dep (scalar_refs expr) -> divider_domain dep)
 (agree : forall dep, divider_domain dep -> VM.find dep env = VM.find dep (stable_env v)) :
 Tool.generated_expr_true expr env <-> Tool.generated_expr_true expr (stable_env v).
Proof.
 unfold Tool.generated_expr_true.
 rewrite (scalar_eval_extensional expr env (stable_env v) env (stable_env v) pure); [reflexivity|].
 intros dep occurs. apply agree. exact (dependencies dep occurs).
Qed.
Lemma assertion_0_guard_transfer env v
 (agree : forall dep, divider_domain dep -> VM.find dep env = VM.find dep (stable_env v)) :
 Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8))) (@Eref VarOrder.T (@Eid VarOrder.T 18))) (@Eref VarOrder.T (@Eid VarOrder.T 423))) (@Econst VarOrder.T (Fuint 1) [::true])) env <-> Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8))) (@Eref VarOrder.T (@Eid VarOrder.T 18))) (@Eref VarOrder.T (@Eid VarOrder.T 423))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env v).
Proof. eapply generated_expr_transfer; [reflexivity| |exact agree].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity.
Qed.
Lemma assertion_0_predicate_transfer env v
 (agree : forall dep, divider_domain dep -> VM.find dep env = VM.find dep (stable_env v)) :
 Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 421)) env <-> Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 421)) (stable_env v).
Proof. eapply generated_expr_transfer; [reflexivity| |exact agree].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity.
Qed.
Lemma assertion_0_local_transfer env v
 (agree : forall dep, divider_domain dep -> VM.find dep env = VM.find dep (stable_env v)) :
 Tool.generated_assert_m0_0_local env <-> Tool.generated_assert_m0_0_local (stable_env v).
Proof.
 have G := assertion_0_guard_transfer env v agree.
 have P := assertion_0_predicate_transfer env v agree.
 unfold Tool.generated_assert_m0_0_local. tauto.
Qed.
Lemma assertion_0_instance states env (found : SVM.find [::] states = Some env) :
 Tool.generated_assert_m0_0_all states <-> Tool.generated_assert_m0_0_local env.
Proof.
 unfold Tool.generated_assert_m0_0_all. rewrite generated_modules_match generated_top_match divider_instances_computed.
 change (((false = true) \/ match SVM.find [::] states with Some sem => Tool.generated_assert_m0_0_local sem | None => False end) /\ True <-> Tool.generated_assert_m0_0_local env).
 rewrite found. split; [intros [[bad|H] _]; [discriminate|exact H]|intro H; split; [right; exact H|exact I]].
Qed.
Lemma assertion_1_guard_transfer env v
 (agree : forall dep, divider_domain dep -> VM.find dep env = VM.find dep (stable_env v)) :
 Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8))) (@Eref VarOrder.T (@Eid VarOrder.T 18))) (@Eref VarOrder.T (@Eid VarOrder.T 428))) (@Econst VarOrder.T (Fuint 1) [::true])) env <-> Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8))) (@Eref VarOrder.T (@Eid VarOrder.T 18))) (@Eref VarOrder.T (@Eid VarOrder.T 428))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env v).
Proof. eapply generated_expr_transfer; [reflexivity| |exact agree].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity.
Qed.
Lemma assertion_1_predicate_transfer env v
 (agree : forall dep, divider_domain dep -> VM.find dep env = VM.find dep (stable_env v)) :
 Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 426)) env <-> Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 426)) (stable_env v).
Proof. eapply generated_expr_transfer; [reflexivity| |exact agree].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity.
Qed.
Lemma assertion_1_local_transfer env v
 (agree : forall dep, divider_domain dep -> VM.find dep env = VM.find dep (stable_env v)) :
 Tool.generated_assert_m0_1_local env <-> Tool.generated_assert_m0_1_local (stable_env v).
Proof.
 have G := assertion_1_guard_transfer env v agree.
 have P := assertion_1_predicate_transfer env v agree.
 unfold Tool.generated_assert_m0_1_local. tauto.
Qed.
Lemma assertion_1_instance states env (found : SVM.find [::] states = Some env) :
 Tool.generated_assert_m0_1_all states <-> Tool.generated_assert_m0_1_local env.
Proof.
 unfold Tool.generated_assert_m0_1_all. rewrite generated_modules_match generated_top_match divider_instances_computed.
 change (((false = true) \/ match SVM.find [::] states with Some sem => Tool.generated_assert_m0_1_local sem | None => False end) /\ True <-> Tool.generated_assert_m0_1_local env).
 rewrite found. split; [intros [[bad|H] _]; [discriminate|exact H]|intro H; split; [right; exact H|exact I]].
Qed.
Lemma assertion_2_guard_transfer env v
 (agree : forall dep, divider_domain dep -> VM.find dep env = VM.find dep (stable_env v)) :
 Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8))) (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 18)) (@Econst VarOrder.T (Fuint 1) [::false]))) (@Eref VarOrder.T (@Eid VarOrder.T 432))) (@Econst VarOrder.T (Fuint 1) [::true])) env <-> Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8))) (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 18)) (@Econst VarOrder.T (Fuint 1) [::false]))) (@Eref VarOrder.T (@Eid VarOrder.T 432))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env v).
Proof. eapply generated_expr_transfer; [reflexivity| |exact agree].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity.
Qed.
Lemma assertion_2_predicate_transfer env v
 (agree : forall dep, divider_domain dep -> VM.find dep env = VM.find dep (stable_env v)) :
 Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 430)) env <-> Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 430)) (stable_env v).
Proof. eapply generated_expr_transfer; [reflexivity| |exact agree].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity.
Qed.
Lemma assertion_2_local_transfer env v
 (agree : forall dep, divider_domain dep -> VM.find dep env = VM.find dep (stable_env v)) :
 Tool.generated_assert_m0_2_local env <-> Tool.generated_assert_m0_2_local (stable_env v).
Proof.
 have G := assertion_2_guard_transfer env v agree.
 have P := assertion_2_predicate_transfer env v agree.
 unfold Tool.generated_assert_m0_2_local. tauto.
Qed.
Lemma assertion_2_instance states env (found : SVM.find [::] states = Some env) :
 Tool.generated_assert_m0_2_all states <-> Tool.generated_assert_m0_2_local env.
Proof.
 unfold Tool.generated_assert_m0_2_all. rewrite generated_modules_match generated_top_match divider_instances_computed.
 change (((false = true) \/ match SVM.find [::] states with Some sem => Tool.generated_assert_m0_2_local sem | None => False end) /\ True <-> Tool.generated_assert_m0_2_local env).
 rewrite found. split; [intros [[bad|H] _]; [discriminate|exact H]|intro H; split; [right; exact H|exact I]].
Qed.
Lemma assertion_3_guard_transfer env v
 (agree : forall dep, divider_domain dep -> VM.find dep env = VM.find dep (stable_env v)) :
 Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8))) (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 18)) (@Econst VarOrder.T (Fuint 1) [::false]))) (@Eref VarOrder.T (@Eid VarOrder.T 439))) (@Econst VarOrder.T (Fuint 1) [::true])) env <-> Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8))) (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 18)) (@Econst VarOrder.T (Fuint 1) [::false]))) (@Eref VarOrder.T (@Eid VarOrder.T 439))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env v).
Proof. eapply generated_expr_transfer; [reflexivity| |exact agree].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity.
Qed.
Lemma assertion_3_predicate_transfer env v
 (agree : forall dep, divider_domain dep -> VM.find dep env = VM.find dep (stable_env v)) :
 Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 437)) env <-> Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 437)) (stable_env v).
Proof. eapply generated_expr_transfer; [reflexivity| |exact agree].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity.
Qed.
Lemma assertion_3_local_transfer env v
 (agree : forall dep, divider_domain dep -> VM.find dep env = VM.find dep (stable_env v)) :
 Tool.generated_assert_m0_3_local env <-> Tool.generated_assert_m0_3_local (stable_env v).
Proof.
 have G := assertion_3_guard_transfer env v agree.
 have P := assertion_3_predicate_transfer env v agree.
 unfold Tool.generated_assert_m0_3_local. tauto.
Qed.
Lemma assertion_3_instance states env (found : SVM.find [::] states = Some env) :
 Tool.generated_assert_m0_3_all states <-> Tool.generated_assert_m0_3_local env.
Proof.
 unfold Tool.generated_assert_m0_3_all. rewrite generated_modules_match generated_top_match divider_instances_computed.
 change (((false = true) \/ match SVM.find [::] states with Some sem => Tool.generated_assert_m0_3_local sem | None => False end) /\ True <-> Tool.generated_assert_m0_3_local env).
 rewrite found. split; [intros [[bad|H] _]; [discriminate|exact H]|intro H; split; [right; exact H|exact I]].
Qed.
Lemma assertion_4_guard_transfer env v
 (agree : forall dep, divider_domain dep -> VM.find dep env = VM.find dep (stable_env v)) :
 Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8))) (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 18)) (@Econst VarOrder.T (Fuint 1) [::false]))) (@Eref VarOrder.T (@Eid VarOrder.T 443))) (@Econst VarOrder.T (Fuint 1) [::true])) env <-> Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8))) (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 18)) (@Econst VarOrder.T (Fuint 1) [::false]))) (@Eref VarOrder.T (@Eid VarOrder.T 443))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env v).
Proof. eapply generated_expr_transfer; [reflexivity| |exact agree].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity.
Qed.
Lemma assertion_4_predicate_transfer env v
 (agree : forall dep, divider_domain dep -> VM.find dep env = VM.find dep (stable_env v)) :
 Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 441)) env <-> Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 441)) (stable_env v).
Proof. eapply generated_expr_transfer; [reflexivity| |exact agree].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity.
Qed.
Lemma assertion_4_local_transfer env v
 (agree : forall dep, divider_domain dep -> VM.find dep env = VM.find dep (stable_env v)) :
 Tool.generated_assert_m0_4_local env <-> Tool.generated_assert_m0_4_local (stable_env v).
Proof.
 have G := assertion_4_guard_transfer env v agree.
 have P := assertion_4_predicate_transfer env v agree.
 unfold Tool.generated_assert_m0_4_local. tauto.
Qed.
Lemma assertion_4_instance states env (found : SVM.find [::] states = Some env) :
 Tool.generated_assert_m0_4_all states <-> Tool.generated_assert_m0_4_local env.
Proof.
 unfold Tool.generated_assert_m0_4_all. rewrite generated_modules_match generated_top_match divider_instances_computed.
 change (((false = true) \/ match SVM.find [::] states with Some sem => Tool.generated_assert_m0_4_local sem | None => False end) /\ True <-> Tool.generated_assert_m0_4_local env).
 rewrite found. split; [intros [[bad|H] _]; [discriminate|exact H]|intro H; split; [right; exact H|exact I]].
Qed.
Lemma assertion_5_guard_transfer env v
 (agree : forall dep, divider_domain dep -> VM.find dep env = VM.find dep (stable_env v)) :
 Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 445))) (@Eref VarOrder.T (@Eid VarOrder.T 448))) (@Eref VarOrder.T (@Eid VarOrder.T 451))) (@Econst VarOrder.T (Fuint 1) [::true])) env <-> Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 445))) (@Eref VarOrder.T (@Eid VarOrder.T 448))) (@Eref VarOrder.T (@Eid VarOrder.T 451))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env v).
Proof. eapply generated_expr_transfer; [reflexivity| |exact agree].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity.
Qed.
Lemma assertion_5_predicate_transfer env v
 (agree : forall dep, divider_domain dep -> VM.find dep env = VM.find dep (stable_env v)) :
 Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 449)) env <-> Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 449)) (stable_env v).
Proof. eapply generated_expr_transfer; [reflexivity| |exact agree].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity.
Qed.
Lemma assertion_5_local_transfer env v
 (agree : forall dep, divider_domain dep -> VM.find dep env = VM.find dep (stable_env v)) :
 Tool.generated_assert_m0_5_local env <-> Tool.generated_assert_m0_5_local (stable_env v).
Proof.
 have G := assertion_5_guard_transfer env v agree.
 have P := assertion_5_predicate_transfer env v agree.
 unfold Tool.generated_assert_m0_5_local. tauto.
Qed.
Lemma assertion_5_instance states env (found : SVM.find [::] states = Some env) :
 Tool.generated_assert_m0_5_all states <-> Tool.generated_assert_m0_5_local env.
Proof.
 unfold Tool.generated_assert_m0_5_all. rewrite generated_modules_match generated_top_match divider_instances_computed.
 change (((false = true) \/ match SVM.find [::] states with Some sem => Tool.generated_assert_m0_5_local sem | None => False end) /\ True <-> Tool.generated_assert_m0_5_local env).
 rewrite found. split; [intros [[bad|H] _]; [discriminate|exact H]|intro H; split; [right; exact H|exact I]].
Qed.
Lemma assertion_6_guard_transfer env v
 (agree : forall dep, divider_domain dep -> VM.find dep env = VM.find dep (stable_env v)) :
 Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 445))) (@Eref VarOrder.T (@Eid VarOrder.T 453))) (@Eref VarOrder.T (@Eid VarOrder.T 456))) (@Econst VarOrder.T (Fuint 1) [::true])) env <-> Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 445))) (@Eref VarOrder.T (@Eid VarOrder.T 453))) (@Eref VarOrder.T (@Eid VarOrder.T 456))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env v).
Proof. eapply generated_expr_transfer; [reflexivity| |exact agree].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity.
Qed.
Lemma assertion_6_predicate_transfer env v
 (agree : forall dep, divider_domain dep -> VM.find dep env = VM.find dep (stable_env v)) :
 Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 454)) env <-> Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 454)) (stable_env v).
Proof. eapply generated_expr_transfer; [reflexivity| |exact agree].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity.
Qed.
Lemma assertion_6_local_transfer env v
 (agree : forall dep, divider_domain dep -> VM.find dep env = VM.find dep (stable_env v)) :
 Tool.generated_assert_m0_6_local env <-> Tool.generated_assert_m0_6_local (stable_env v).
Proof.
 have G := assertion_6_guard_transfer env v agree.
 have P := assertion_6_predicate_transfer env v agree.
 unfold Tool.generated_assert_m0_6_local. tauto.
Qed.
Lemma assertion_6_instance states env (found : SVM.find [::] states = Some env) :
 Tool.generated_assert_m0_6_all states <-> Tool.generated_assert_m0_6_local env.
Proof.
 unfold Tool.generated_assert_m0_6_all. rewrite generated_modules_match generated_top_match divider_instances_computed.
 change (((false = true) \/ match SVM.find [::] states with Some sem => Tool.generated_assert_m0_6_local sem | None => False end) /\ True <-> Tool.generated_assert_m0_6_local env).
 rewrite found. split; [intros [[bad|H] _]; [discriminate|exact H]|intro H; split; [right; exact H|exact I]].
Qed.
Lemma assertion_7_guard_transfer env v
 (agree : forall dep, divider_domain dep -> VM.find dep env = VM.find dep (stable_env v)) :
 Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 445))) (@Eref VarOrder.T (@Eid VarOrder.T 458))) (@Eref VarOrder.T (@Eid VarOrder.T 463))) (@Econst VarOrder.T (Fuint 1) [::true])) env <-> Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 445))) (@Eref VarOrder.T (@Eid VarOrder.T 458))) (@Eref VarOrder.T (@Eid VarOrder.T 463))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env v).
Proof. eapply generated_expr_transfer; [reflexivity| |exact agree].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity.
Qed.
Lemma assertion_7_predicate_transfer env v
 (agree : forall dep, divider_domain dep -> VM.find dep env = VM.find dep (stable_env v)) :
 Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 461)) env <-> Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 461)) (stable_env v).
Proof. eapply generated_expr_transfer; [reflexivity| |exact agree].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity.
Qed.
Lemma assertion_7_local_transfer env v
 (agree : forall dep, divider_domain dep -> VM.find dep env = VM.find dep (stable_env v)) :
 Tool.generated_assert_m0_7_local env <-> Tool.generated_assert_m0_7_local (stable_env v).
Proof.
 have G := assertion_7_guard_transfer env v agree.
 have P := assertion_7_predicate_transfer env v agree.
 unfold Tool.generated_assert_m0_7_local. tauto.
Qed.
Lemma assertion_7_instance states env (found : SVM.find [::] states = Some env) :
 Tool.generated_assert_m0_7_all states <-> Tool.generated_assert_m0_7_local env.
Proof.
 unfold Tool.generated_assert_m0_7_all. rewrite generated_modules_match generated_top_match divider_instances_computed.
 change (((false = true) \/ match SVM.find [::] states with Some sem => Tool.generated_assert_m0_7_local sem | None => False end) /\ True <-> Tool.generated_assert_m0_7_local env).
 rewrite found. split; [intros [[bad|H] _]; [discriminate|exact H]|intro H; split; [right; exact H|exact I]].
Qed.
Lemma assertion_8_guard_transfer env v
 (agree : forall dep, divider_domain dep -> VM.find dep env = VM.find dep (stable_env v)) :
 Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 445))) (@Eref VarOrder.T (@Eid VarOrder.T 458))) (@Eref VarOrder.T (@Eid VarOrder.T 471))) (@Econst VarOrder.T (Fuint 1) [::true])) env <-> Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 445))) (@Eref VarOrder.T (@Eid VarOrder.T 458))) (@Eref VarOrder.T (@Eid VarOrder.T 471))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env v).
Proof. eapply generated_expr_transfer; [reflexivity| |exact agree].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity.
Qed.
Lemma assertion_8_predicate_transfer env v
 (agree : forall dep, divider_domain dep -> VM.find dep env = VM.find dep (stable_env v)) :
 Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 469)) env <-> Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 469)) (stable_env v).
Proof. eapply generated_expr_transfer; [reflexivity| |exact agree].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity.
Qed.
Lemma assertion_8_local_transfer env v
 (agree : forall dep, divider_domain dep -> VM.find dep env = VM.find dep (stable_env v)) :
 Tool.generated_assert_m0_8_local env <-> Tool.generated_assert_m0_8_local (stable_env v).
Proof.
 have G := assertion_8_guard_transfer env v agree.
 have P := assertion_8_predicate_transfer env v agree.
 unfold Tool.generated_assert_m0_8_local. tauto.
Qed.
Lemma assertion_8_instance states env (found : SVM.find [::] states = Some env) :
 Tool.generated_assert_m0_8_all states <-> Tool.generated_assert_m0_8_local env.
Proof.
 unfold Tool.generated_assert_m0_8_all. rewrite generated_modules_match generated_top_match divider_instances_computed.
 change (((false = true) \/ match SVM.find [::] states with Some sem => Tool.generated_assert_m0_8_local sem | None => False end) /\ True <-> Tool.generated_assert_m0_8_local env).
 rewrite found. split; [intros [[bad|H] _]; [discriminate|exact H]|intro H; split; [right; exact H|exact I]].
Qed.
Lemma assertion_9_guard_transfer env v
 (agree : forall dep, divider_domain dep -> VM.find dep env = VM.find dep (stable_env v)) :
 Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 475))) (@Eref VarOrder.T (@Eid VarOrder.T 478))) (@Econst VarOrder.T (Fuint 1) [::true])) env <-> Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 475))) (@Eref VarOrder.T (@Eid VarOrder.T 478))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env v).
Proof. eapply generated_expr_transfer; [reflexivity| |exact agree].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity.
Qed.
Lemma assertion_9_predicate_transfer env v
 (agree : forall dep, divider_domain dep -> VM.find dep env = VM.find dep (stable_env v)) :
 Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 8)) env <-> Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 8)) (stable_env v).
Proof. eapply generated_expr_transfer; [reflexivity| |exact agree].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity.
Qed.
Lemma assertion_9_local_transfer env v
 (agree : forall dep, divider_domain dep -> VM.find dep env = VM.find dep (stable_env v)) :
 Tool.generated_assert_m0_9_local env <-> Tool.generated_assert_m0_9_local (stable_env v).
Proof.
 have G := assertion_9_guard_transfer env v agree.
 have P := assertion_9_predicate_transfer env v agree.
 unfold Tool.generated_assert_m0_9_local. tauto.
Qed.
Lemma assertion_9_instance states env (found : SVM.find [::] states = Some env) :
 Tool.generated_assert_m0_9_all states <-> Tool.generated_assert_m0_9_local env.
Proof.
 unfold Tool.generated_assert_m0_9_all. rewrite generated_modules_match generated_top_match divider_instances_computed.
 change (((false = true) \/ match SVM.find [::] states with Some sem => Tool.generated_assert_m0_9_local sem | None => False end) /\ True <-> Tool.generated_assert_m0_9_local env).
 rewrite found. split; [intros [[bad|H] _]; [discriminate|exact H]|intro H; split; [right; exact H|exact I]].
Qed.
Lemma assertion_10_guard_transfer env v
 (agree : forall dep, divider_domain dep -> VM.find dep env = VM.find dep (stable_env v)) :
 Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 475))) (@Eref VarOrder.T (@Eid VarOrder.T 482))) (@Econst VarOrder.T (Fuint 1) [::true])) env <-> Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 475))) (@Eref VarOrder.T (@Eid VarOrder.T 482))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env v).
Proof. eapply generated_expr_transfer; [reflexivity| |exact agree].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity.
Qed.
Lemma assertion_10_predicate_transfer env v
 (agree : forall dep, divider_domain dep -> VM.find dep env = VM.find dep (stable_env v)) :
 Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 480)) env <-> Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 480)) (stable_env v).
Proof. eapply generated_expr_transfer; [reflexivity| |exact agree].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity.
Qed.
Lemma assertion_10_local_transfer env v
 (agree : forall dep, divider_domain dep -> VM.find dep env = VM.find dep (stable_env v)) :
 Tool.generated_assert_m0_10_local env <-> Tool.generated_assert_m0_10_local (stable_env v).
Proof.
 have G := assertion_10_guard_transfer env v agree.
 have P := assertion_10_predicate_transfer env v agree.
 unfold Tool.generated_assert_m0_10_local. tauto.
Qed.
Lemma assertion_10_instance states env (found : SVM.find [::] states = Some env) :
 Tool.generated_assert_m0_10_all states <-> Tool.generated_assert_m0_10_local env.
Proof.
 unfold Tool.generated_assert_m0_10_all. rewrite generated_modules_match generated_top_match divider_instances_computed.
 change (((false = true) \/ match SVM.find [::] states with Some sem => Tool.generated_assert_m0_10_local sem | None => False end) /\ True <-> Tool.generated_assert_m0_10_local env).
 rewrite found. split; [intros [[bad|H] _]; [discriminate|exact H]|intro H; split; [right; exact H|exact I]].
Qed.
Print Assumptions assertion_10_local_transfer.
Print Assumptions assertion_10_instance.
