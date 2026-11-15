From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import ScalarEvaluation ScalarExtensionality.
From Divider Require Import Stable NodeProgress RuntimeRepresentation AssertTransfer.
Local Open Scope N_scope.
Lemma private_expr_clock expr v clock
 (pure:scalar_exprb expr)
 (dependencies:forall dep, List.In dep (scalar_refs expr) -> divider_domain dep /\ dep <> 0) :
 Tool.generated_expr_true expr (stable_env (with_clock v clock)) <-> Tool.generated_expr_true expr (stable_env v).
Proof.
 unfold Tool.generated_expr_true.
 rewrite (scalar_eval_extensional expr (stable_env (with_clock v clock)) (stable_env v) (stable_env (with_clock v clock)) (stable_env v) pure); [reflexivity|].
 intros dep occurs. destruct (dependencies dep occurs) as [inside nonclock].
 apply stable_clock_private; assumption.
Qed.
Lemma assertion_0_guard_clock v clock :
 Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8))) (@Eref VarOrder.T (@Eid VarOrder.T 18))) (@Eref VarOrder.T (@Eid VarOrder.T 423))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env (with_clock v clock)) <-> Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8))) (@Eref VarOrder.T (@Eid VarOrder.T 18))) (@Eref VarOrder.T (@Eid VarOrder.T 423))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env v).
Proof. apply private_expr_clock; [reflexivity|].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; (split; [vm_compute; reflexivity|discriminate]).
Qed.
Lemma assertion_0_predicate_clock v clock :
 Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 421)) (stable_env (with_clock v clock)) <-> Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 421)) (stable_env v).
Proof. apply private_expr_clock; [reflexivity|].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; (split; [vm_compute; reflexivity|discriminate]).
Qed.
Lemma assertion_0_local_clock v clock :
 Tool.generated_assert_m0_0_local (stable_env (with_clock v clock)) <-> Tool.generated_assert_m0_0_local (stable_env v).
Proof.
 unfold Tool.generated_assert_m0_0_local.
 have G := assertion_0_guard_clock v clock.
 have P := assertion_0_predicate_clock v clock. split; intros H E.
 - apply (proj1 P). apply H. apply (proj2 G). exact E.
 - apply (proj2 P). apply H. apply (proj1 G). exact E.
Qed.
Lemma assertion_1_guard_clock v clock :
 Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8))) (@Eref VarOrder.T (@Eid VarOrder.T 18))) (@Eref VarOrder.T (@Eid VarOrder.T 428))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env (with_clock v clock)) <-> Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8))) (@Eref VarOrder.T (@Eid VarOrder.T 18))) (@Eref VarOrder.T (@Eid VarOrder.T 428))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env v).
Proof. apply private_expr_clock; [reflexivity|].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; (split; [vm_compute; reflexivity|discriminate]).
Qed.
Lemma assertion_1_predicate_clock v clock :
 Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 426)) (stable_env (with_clock v clock)) <-> Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 426)) (stable_env v).
Proof. apply private_expr_clock; [reflexivity|].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; (split; [vm_compute; reflexivity|discriminate]).
Qed.
Lemma assertion_1_local_clock v clock :
 Tool.generated_assert_m0_1_local (stable_env (with_clock v clock)) <-> Tool.generated_assert_m0_1_local (stable_env v).
Proof.
 unfold Tool.generated_assert_m0_1_local.
 have G := assertion_1_guard_clock v clock.
 have P := assertion_1_predicate_clock v clock. split; intros H E.
 - apply (proj1 P). apply H. apply (proj2 G). exact E.
 - apply (proj2 P). apply H. apply (proj1 G). exact E.
Qed.
Lemma assertion_2_guard_clock v clock :
 Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8))) (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 18)) (@Econst VarOrder.T (Fuint 1) [::false]))) (@Eref VarOrder.T (@Eid VarOrder.T 432))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env (with_clock v clock)) <-> Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8))) (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 18)) (@Econst VarOrder.T (Fuint 1) [::false]))) (@Eref VarOrder.T (@Eid VarOrder.T 432))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env v).
Proof. apply private_expr_clock; [reflexivity|].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; (split; [vm_compute; reflexivity|discriminate]).
Qed.
Lemma assertion_2_predicate_clock v clock :
 Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 430)) (stable_env (with_clock v clock)) <-> Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 430)) (stable_env v).
Proof. apply private_expr_clock; [reflexivity|].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; (split; [vm_compute; reflexivity|discriminate]).
Qed.
Lemma assertion_2_local_clock v clock :
 Tool.generated_assert_m0_2_local (stable_env (with_clock v clock)) <-> Tool.generated_assert_m0_2_local (stable_env v).
Proof.
 unfold Tool.generated_assert_m0_2_local.
 have G := assertion_2_guard_clock v clock.
 have P := assertion_2_predicate_clock v clock. split; intros H E.
 - apply (proj1 P). apply H. apply (proj2 G). exact E.
 - apply (proj2 P). apply H. apply (proj1 G). exact E.
Qed.
Lemma assertion_3_guard_clock v clock :
 Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8))) (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 18)) (@Econst VarOrder.T (Fuint 1) [::false]))) (@Eref VarOrder.T (@Eid VarOrder.T 439))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env (with_clock v clock)) <-> Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8))) (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 18)) (@Econst VarOrder.T (Fuint 1) [::false]))) (@Eref VarOrder.T (@Eid VarOrder.T 439))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env v).
Proof. apply private_expr_clock; [reflexivity|].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; (split; [vm_compute; reflexivity|discriminate]).
Qed.
Lemma assertion_3_predicate_clock v clock :
 Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 437)) (stable_env (with_clock v clock)) <-> Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 437)) (stable_env v).
Proof. apply private_expr_clock; [reflexivity|].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; (split; [vm_compute; reflexivity|discriminate]).
Qed.
Lemma assertion_3_local_clock v clock :
 Tool.generated_assert_m0_3_local (stable_env (with_clock v clock)) <-> Tool.generated_assert_m0_3_local (stable_env v).
Proof.
 unfold Tool.generated_assert_m0_3_local.
 have G := assertion_3_guard_clock v clock.
 have P := assertion_3_predicate_clock v clock. split; intros H E.
 - apply (proj1 P). apply H. apply (proj2 G). exact E.
 - apply (proj2 P). apply H. apply (proj1 G). exact E.
Qed.
Lemma assertion_4_guard_clock v clock :
 Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8))) (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 18)) (@Econst VarOrder.T (Fuint 1) [::false]))) (@Eref VarOrder.T (@Eid VarOrder.T 443))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env (with_clock v clock)) <-> Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8))) (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 18)) (@Econst VarOrder.T (Fuint 1) [::false]))) (@Eref VarOrder.T (@Eid VarOrder.T 443))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env v).
Proof. apply private_expr_clock; [reflexivity|].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; (split; [vm_compute; reflexivity|discriminate]).
Qed.
Lemma assertion_4_predicate_clock v clock :
 Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 441)) (stable_env (with_clock v clock)) <-> Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 441)) (stable_env v).
Proof. apply private_expr_clock; [reflexivity|].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; (split; [vm_compute; reflexivity|discriminate]).
Qed.
Lemma assertion_4_local_clock v clock :
 Tool.generated_assert_m0_4_local (stable_env (with_clock v clock)) <-> Tool.generated_assert_m0_4_local (stable_env v).
Proof.
 unfold Tool.generated_assert_m0_4_local.
 have G := assertion_4_guard_clock v clock.
 have P := assertion_4_predicate_clock v clock. split; intros H E.
 - apply (proj1 P). apply H. apply (proj2 G). exact E.
 - apply (proj2 P). apply H. apply (proj1 G). exact E.
Qed.
Lemma assertion_5_guard_clock v clock :
 Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 445))) (@Eref VarOrder.T (@Eid VarOrder.T 448))) (@Eref VarOrder.T (@Eid VarOrder.T 451))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env (with_clock v clock)) <-> Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 445))) (@Eref VarOrder.T (@Eid VarOrder.T 448))) (@Eref VarOrder.T (@Eid VarOrder.T 451))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env v).
Proof. apply private_expr_clock; [reflexivity|].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; (split; [vm_compute; reflexivity|discriminate]).
Qed.
Lemma assertion_5_predicate_clock v clock :
 Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 449)) (stable_env (with_clock v clock)) <-> Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 449)) (stable_env v).
Proof. apply private_expr_clock; [reflexivity|].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; (split; [vm_compute; reflexivity|discriminate]).
Qed.
Lemma assertion_5_local_clock v clock :
 Tool.generated_assert_m0_5_local (stable_env (with_clock v clock)) <-> Tool.generated_assert_m0_5_local (stable_env v).
Proof.
 unfold Tool.generated_assert_m0_5_local.
 have G := assertion_5_guard_clock v clock.
 have P := assertion_5_predicate_clock v clock. split; intros H E.
 - apply (proj1 P). apply H. apply (proj2 G). exact E.
 - apply (proj2 P). apply H. apply (proj1 G). exact E.
Qed.
Lemma assertion_6_guard_clock v clock :
 Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 445))) (@Eref VarOrder.T (@Eid VarOrder.T 453))) (@Eref VarOrder.T (@Eid VarOrder.T 456))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env (with_clock v clock)) <-> Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 445))) (@Eref VarOrder.T (@Eid VarOrder.T 453))) (@Eref VarOrder.T (@Eid VarOrder.T 456))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env v).
Proof. apply private_expr_clock; [reflexivity|].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; (split; [vm_compute; reflexivity|discriminate]).
Qed.
Lemma assertion_6_predicate_clock v clock :
 Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 454)) (stable_env (with_clock v clock)) <-> Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 454)) (stable_env v).
Proof. apply private_expr_clock; [reflexivity|].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; (split; [vm_compute; reflexivity|discriminate]).
Qed.
Lemma assertion_6_local_clock v clock :
 Tool.generated_assert_m0_6_local (stable_env (with_clock v clock)) <-> Tool.generated_assert_m0_6_local (stable_env v).
Proof.
 unfold Tool.generated_assert_m0_6_local.
 have G := assertion_6_guard_clock v clock.
 have P := assertion_6_predicate_clock v clock. split; intros H E.
 - apply (proj1 P). apply H. apply (proj2 G). exact E.
 - apply (proj2 P). apply H. apply (proj1 G). exact E.
Qed.
Lemma assertion_7_guard_clock v clock :
 Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 445))) (@Eref VarOrder.T (@Eid VarOrder.T 458))) (@Eref VarOrder.T (@Eid VarOrder.T 463))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env (with_clock v clock)) <-> Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 445))) (@Eref VarOrder.T (@Eid VarOrder.T 458))) (@Eref VarOrder.T (@Eid VarOrder.T 463))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env v).
Proof. apply private_expr_clock; [reflexivity|].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; (split; [vm_compute; reflexivity|discriminate]).
Qed.
Lemma assertion_7_predicate_clock v clock :
 Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 461)) (stable_env (with_clock v clock)) <-> Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 461)) (stable_env v).
Proof. apply private_expr_clock; [reflexivity|].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; (split; [vm_compute; reflexivity|discriminate]).
Qed.
Lemma assertion_7_local_clock v clock :
 Tool.generated_assert_m0_7_local (stable_env (with_clock v clock)) <-> Tool.generated_assert_m0_7_local (stable_env v).
Proof.
 unfold Tool.generated_assert_m0_7_local.
 have G := assertion_7_guard_clock v clock.
 have P := assertion_7_predicate_clock v clock. split; intros H E.
 - apply (proj1 P). apply H. apply (proj2 G). exact E.
 - apply (proj2 P). apply H. apply (proj1 G). exact E.
Qed.
Lemma assertion_8_guard_clock v clock :
 Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 445))) (@Eref VarOrder.T (@Eid VarOrder.T 458))) (@Eref VarOrder.T (@Eid VarOrder.T 471))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env (with_clock v clock)) <-> Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 445))) (@Eref VarOrder.T (@Eid VarOrder.T 458))) (@Eref VarOrder.T (@Eid VarOrder.T 471))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env v).
Proof. apply private_expr_clock; [reflexivity|].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; (split; [vm_compute; reflexivity|discriminate]).
Qed.
Lemma assertion_8_predicate_clock v clock :
 Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 469)) (stable_env (with_clock v clock)) <-> Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 469)) (stable_env v).
Proof. apply private_expr_clock; [reflexivity|].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; (split; [vm_compute; reflexivity|discriminate]).
Qed.
Lemma assertion_8_local_clock v clock :
 Tool.generated_assert_m0_8_local (stable_env (with_clock v clock)) <-> Tool.generated_assert_m0_8_local (stable_env v).
Proof.
 unfold Tool.generated_assert_m0_8_local.
 have G := assertion_8_guard_clock v clock.
 have P := assertion_8_predicate_clock v clock. split; intros H E.
 - apply (proj1 P). apply H. apply (proj2 G). exact E.
 - apply (proj2 P). apply H. apply (proj1 G). exact E.
Qed.
Lemma assertion_9_guard_clock v clock :
 Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 475))) (@Eref VarOrder.T (@Eid VarOrder.T 478))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env (with_clock v clock)) <-> Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 475))) (@Eref VarOrder.T (@Eid VarOrder.T 478))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env v).
Proof. apply private_expr_clock; [reflexivity|].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; (split; [vm_compute; reflexivity|discriminate]).
Qed.
Lemma assertion_9_predicate_clock v clock :
 Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 8)) (stable_env (with_clock v clock)) <-> Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 8)) (stable_env v).
Proof. apply private_expr_clock; [reflexivity|].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; (split; [vm_compute; reflexivity|discriminate]).
Qed.
Lemma assertion_9_local_clock v clock :
 Tool.generated_assert_m0_9_local (stable_env (with_clock v clock)) <-> Tool.generated_assert_m0_9_local (stable_env v).
Proof.
 unfold Tool.generated_assert_m0_9_local.
 have G := assertion_9_guard_clock v clock.
 have P := assertion_9_predicate_clock v clock. split; intros H E.
 - apply (proj1 P). apply H. apply (proj2 G). exact E.
 - apply (proj2 P). apply H. apply (proj1 G). exact E.
Qed.
Lemma assertion_10_guard_clock v clock :
 Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 475))) (@Eref VarOrder.T (@Eid VarOrder.T 482))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env (with_clock v clock)) <-> Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 475))) (@Eref VarOrder.T (@Eid VarOrder.T 482))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env v).
Proof. apply private_expr_clock; [reflexivity|].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; (split; [vm_compute; reflexivity|discriminate]).
Qed.
Lemma assertion_10_predicate_clock v clock :
 Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 480)) (stable_env (with_clock v clock)) <-> Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 480)) (stable_env v).
Proof. apply private_expr_clock; [reflexivity|].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; (split; [vm_compute; reflexivity|discriminate]).
Qed.
Lemma assertion_10_local_clock v clock :
 Tool.generated_assert_m0_10_local (stable_env (with_clock v clock)) <-> Tool.generated_assert_m0_10_local (stable_env v).
Proof.
 unfold Tool.generated_assert_m0_10_local.
 have G := assertion_10_guard_clock v clock.
 have P := assertion_10_predicate_clock v clock. split; intros H E.
 - apply (proj1 P). apply H. apply (proj2 G). exact E.
 - apply (proj2 P). apply H. apply (proj1 G). exact E.
Qed.
