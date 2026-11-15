From Coq Require Import ZArith List Bool.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths.
From Divider Require Import Stable Representation LeafWords Controls OutputLink AssertTransfer AssertBooleans.
Module OldBits := Generated.Radix2Divider.CIRCTBits.
Local Open Scope Z_scope.
Lemma reference_check_0 s i (checks : Reference.asserts s i)
 (enabled : Reference.v416 s i = 1) : Reference.v414 s i = 1.
Proof.
 unfold Reference.asserts in checks.
 have allchecks := (proj1 (@List.forallb_forall bool (fun b => b) (Reference.assertionChecks s i))) checks.
 have member : List.In (orb (negb (Z.eqb (Reference.v416 s i) 1)) (Z.eqb (Reference.v414 s i) 1)) (Reference.assertionChecks s i).
 { unfold Reference.assertionChecks. left; reflexivity. }
 have valid := allchecks _ member. rewrite enabled Z.eqb_refl in valid.
 cbn [negb orb] in valid. apply Z.eqb_eq. exact valid.
Qed.
Lemma assertion_0_guard_reference s i ghost
 (enabled : Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (8%nat))))) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (18%nat))))) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (423%nat))))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env (encoded_leaves s i ghost))) :
 Reference.v416 s i = 1.
Proof.
 apply (proj1 (assertion_0_guard_integers s i ghost)) in enabled.
 destruct enabled as [H8 [H18 H423]].
 rewrite control_8_reference in H8.
 change (Reference.v399 s i = 1) in H8.
 rewrite leaf_18_integer in H18. change (OldBits.word 1 (Reference.r1_ndivBy0Reg s) = 1) in H18.
 rewrite control_423_reference in H423.
 unfold Reference.v416. rewrite H8 H18 H423. reflexivity.
Qed.
Lemma reference_assertion_0 s i ghost
 (checks : Reference.asserts s i) : Tool.generated_assert_m0_0_local (stable_env (encoded_leaves s i ghost)).
Proof.
 unfold Tool.generated_assert_m0_0_local. intro enabled.
 apply (proj2 (assertion_0_predicate_integer s i ghost)).
 rewrite control_421_reference.
 apply reference_check_0; [exact checks|]. exact (assertion_0_guard_reference s i ghost enabled).
Qed.
Lemma reference_check_1 s i (checks : Reference.asserts s i)
 (enabled : Reference.v416 s i = 1) : Reference.v418 s i = 1.
Proof.
 unfold Reference.asserts in checks.
 have allchecks := (proj1 (@List.forallb_forall bool (fun b => b) (Reference.assertionChecks s i))) checks.
 have member : List.In (orb (negb (Z.eqb (Reference.v416 s i) 1)) (Z.eqb (Reference.v418 s i) 1)) (Reference.assertionChecks s i).
 { unfold Reference.assertionChecks. do 1 right. left; reflexivity. }
 have valid := allchecks _ member. rewrite enabled Z.eqb_refl in valid.
 cbn [negb orb] in valid. apply Z.eqb_eq. exact valid.
Qed.
Lemma assertion_1_guard_reference s i ghost
 (enabled : Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (8%nat))))) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (18%nat))))) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (428%nat))))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env (encoded_leaves s i ghost))) :
 Reference.v416 s i = 1.
Proof.
 apply (proj1 (assertion_1_guard_integers s i ghost)) in enabled.
 destruct enabled as [H8 [H18 H428]].
 rewrite control_8_reference in H8.
 change (Reference.v399 s i = 1) in H8.
 rewrite leaf_18_integer in H18. change (OldBits.word 1 (Reference.r1_ndivBy0Reg s) = 1) in H18.
 rewrite control_428_reference in H428.
 unfold Reference.v416. rewrite H8 H18 H428. reflexivity.
Qed.
Lemma reference_assertion_1 s i ghost
 (checks : Reference.asserts s i) : Tool.generated_assert_m0_1_local (stable_env (encoded_leaves s i ghost)).
Proof.
 unfold Tool.generated_assert_m0_1_local. intro enabled.
 apply (proj2 (assertion_1_predicate_integer s i ghost)).
 rewrite control_426_reference.
 apply reference_check_1; [exact checks|]. exact (assertion_1_guard_reference s i ghost enabled).
Qed.
Lemma reference_check_2 s i (checks : Reference.asserts s i)
 (enabled : Reference.v421 s i = 1) : Reference.v419 s i = 1.
Proof.
 unfold Reference.asserts in checks.
 have allchecks := (proj1 (@List.forallb_forall bool (fun b => b) (Reference.assertionChecks s i))) checks.
 have member : List.In (orb (negb (Z.eqb (Reference.v421 s i) 1)) (Z.eqb (Reference.v419 s i) 1)) (Reference.assertionChecks s i).
 { unfold Reference.assertionChecks. do 2 right. left; reflexivity. }
 have valid := allchecks _ member. rewrite enabled Z.eqb_refl in valid.
 cbn [negb orb] in valid. apply Z.eqb_eq. exact valid.
Qed.
Lemma assertion_2_guard_reference s i ghost
 (enabled : Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (8%nat))))) (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (18%nat)))) (@Econst VarOrder.T (Fuint 1) [::false]))) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (432%nat))))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env (encoded_leaves s i ghost))) :
 Reference.v421 s i = 1.
Proof.
 apply (proj1 (assertion_2_guard_integers s i ghost)) in enabled.
 destruct enabled as [H8 [H18 H432]].
 rewrite control_8_reference in H8.
 change (Reference.v399 s i = 1) in H8.
 rewrite leaf_18_integer in H18. change (OldBits.word 1 (Reference.r1_ndivBy0Reg s) = 0) in H18.
 rewrite control_432_reference in H432.
 unfold Reference.v421, Reference.v420, Reference.v22. rewrite H8 H18 H432. reflexivity.
Qed.
Lemma reference_assertion_2 s i ghost
 (checks : Reference.asserts s i) : Tool.generated_assert_m0_2_local (stable_env (encoded_leaves s i ghost)).
Proof.
 unfold Tool.generated_assert_m0_2_local. intro enabled.
 apply (proj2 (assertion_2_predicate_integer s i ghost)).
 rewrite control_430_reference.
 apply reference_check_2; [exact checks|]. exact (assertion_2_guard_reference s i ghost enabled).
Qed.
Lemma reference_check_3 s i (checks : Reference.asserts s i)
 (enabled : Reference.v421 s i = 1) : Reference.v430 s i = 1.
Proof.
 unfold Reference.asserts in checks.
 have allchecks := (proj1 (@List.forallb_forall bool (fun b => b) (Reference.assertionChecks s i))) checks.
 have member : List.In (orb (negb (Z.eqb (Reference.v421 s i) 1)) (Z.eqb (Reference.v430 s i) 1)) (Reference.assertionChecks s i).
 { unfold Reference.assertionChecks. do 3 right. left; reflexivity. }
 have valid := allchecks _ member. rewrite enabled Z.eqb_refl in valid.
 cbn [negb orb] in valid. apply Z.eqb_eq. exact valid.
Qed.
Lemma assertion_3_guard_reference s i ghost
 (enabled : Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (8%nat))))) (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (18%nat)))) (@Econst VarOrder.T (Fuint 1) [::false]))) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (439%nat))))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env (encoded_leaves s i ghost))) :
 Reference.v421 s i = 1.
Proof.
 apply (proj1 (assertion_3_guard_integers s i ghost)) in enabled.
 destruct enabled as [H8 [H18 H439]].
 rewrite control_8_reference in H8.
 change (Reference.v399 s i = 1) in H8.
 rewrite leaf_18_integer in H18. change (OldBits.word 1 (Reference.r1_ndivBy0Reg s) = 0) in H18.
 rewrite control_439_reference in H439.
 unfold Reference.v421, Reference.v420, Reference.v22. rewrite H8 H18 H439. reflexivity.
Qed.
Lemma reference_assertion_3 s i ghost
 (checks : Reference.asserts s i) : Tool.generated_assert_m0_3_local (stable_env (encoded_leaves s i ghost)).
Proof.
 unfold Tool.generated_assert_m0_3_local. intro enabled.
 apply (proj2 (assertion_3_predicate_integer s i ghost)).
 rewrite control_437_reference.
 apply reference_check_3; [exact checks|]. exact (assertion_3_guard_reference s i ghost enabled).
Qed.
Lemma reference_check_4 s i (checks : Reference.asserts s i)
 (enabled : Reference.v421 s i = 1) : Reference.v431 s i = 1.
Proof.
 unfold Reference.asserts in checks.
 have allchecks := (proj1 (@List.forallb_forall bool (fun b => b) (Reference.assertionChecks s i))) checks.
 have member : List.In (orb (negb (Z.eqb (Reference.v421 s i) 1)) (Z.eqb (Reference.v431 s i) 1)) (Reference.assertionChecks s i).
 { unfold Reference.assertionChecks. do 4 right. left; reflexivity. }
 have valid := allchecks _ member. rewrite enabled Z.eqb_refl in valid.
 cbn [negb orb] in valid. apply Z.eqb_eq. exact valid.
Qed.
Lemma assertion_4_guard_reference s i ghost
 (enabled : Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (8%nat))))) (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (18%nat)))) (@Econst VarOrder.T (Fuint 1) [::false]))) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (443%nat))))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env (encoded_leaves s i ghost))) :
 Reference.v421 s i = 1.
Proof.
 apply (proj1 (assertion_4_guard_integers s i ghost)) in enabled.
 destruct enabled as [H8 [H18 H443]].
 rewrite control_8_reference in H8.
 change (Reference.v399 s i = 1) in H8.
 rewrite leaf_18_integer in H18. change (OldBits.word 1 (Reference.r1_ndivBy0Reg s) = 0) in H18.
 rewrite control_443_reference in H443.
 unfold Reference.v421, Reference.v420, Reference.v22. rewrite H8 H18 H443. reflexivity.
Qed.
Lemma reference_assertion_4 s i ghost
 (checks : Reference.asserts s i) : Tool.generated_assert_m0_4_local (stable_env (encoded_leaves s i ghost)).
Proof.
 unfold Tool.generated_assert_m0_4_local. intro enabled.
 apply (proj2 (assertion_4_predicate_integer s i ghost)).
 rewrite control_441_reference.
 apply reference_check_4; [exact checks|]. exact (assertion_4_guard_reference s i ghost enabled).
Qed.
Lemma reference_check_5 s i (checks : Reference.asserts s i)
 (enabled : Reference.v433 s i = 1) : Reference.v6 s i = 1.
Proof.
 unfold Reference.asserts in checks.
 have allchecks := (proj1 (@List.forallb_forall bool (fun b => b) (Reference.assertionChecks s i))) checks.
 have member : List.In (orb (negb (Z.eqb (Reference.v433 s i) 1)) (Z.eqb (Reference.v6 s i) 1)) (Reference.assertionChecks s i).
 { unfold Reference.assertionChecks. do 5 right. left; reflexivity. }
 have valid := allchecks _ member. rewrite enabled Z.eqb_refl in valid.
 cbn [negb orb] in valid. apply Z.eqb_eq. exact valid.
Qed.
Lemma assertion_5_guard_reference s i ghost
 (enabled : Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (445%nat))))) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (448%nat))))) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (451%nat))))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env (encoded_leaves s i ghost))) :
 Reference.v433 s i = 1.
Proof.
 apply (proj1 (assertion_5_guard_integers s i ghost)) in enabled.
 destruct enabled as [H445 [H448 H451]].
 rewrite leaf_445_integer in H445. change (OldBits.word 1 (Reference.r10_nhistoryValid s) = 1) in H445.
 rewrite control_448_reference in H448.
 rewrite control_451_reference in H451.
 unfold Reference.v433. rewrite H445 H448 H451. reflexivity.
Qed.
Lemma reference_assertion_5 s i ghost
 (checks : Reference.asserts s i) : Tool.generated_assert_m0_5_local (stable_env (encoded_leaves s i ghost)).
Proof.
 unfold Tool.generated_assert_m0_5_local. intro enabled.
 apply (proj2 (assertion_5_predicate_integer s i ghost)).
 rewrite control_449_reference.
 apply reference_check_5; [exact checks|]. exact (assertion_5_guard_reference s i ghost enabled).
Qed.
Lemma reference_check_6 s i (checks : Reference.asserts s i)
 (enabled : Reference.v435 s i = 1) : Reference.v8 s i = 1.
Proof.
 unfold Reference.asserts in checks.
 have allchecks := (proj1 (@List.forallb_forall bool (fun b => b) (Reference.assertionChecks s i))) checks.
 have member : List.In (orb (negb (Z.eqb (Reference.v435 s i) 1)) (Z.eqb (Reference.v8 s i) 1)) (Reference.assertionChecks s i).
 { unfold Reference.assertionChecks. do 6 right. left; reflexivity. }
 have valid := allchecks _ member. rewrite enabled Z.eqb_refl in valid.
 cbn [negb orb] in valid. apply Z.eqb_eq. exact valid.
Qed.
Lemma assertion_6_guard_reference s i ghost
 (enabled : Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (445%nat))))) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (453%nat))))) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (456%nat))))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env (encoded_leaves s i ghost))) :
 Reference.v435 s i = 1.
Proof.
 apply (proj1 (assertion_6_guard_integers s i ghost)) in enabled.
 destruct enabled as [H445 [H453 H456]].
 rewrite leaf_445_integer in H445. change (OldBits.word 1 (Reference.r10_nhistoryValid s) = 1) in H445.
 rewrite control_453_reference in H453.
 rewrite control_456_reference in H456.
 unfold Reference.v435. rewrite H445 H453 H456. reflexivity.
Qed.
Lemma reference_assertion_6 s i ghost
 (checks : Reference.asserts s i) : Tool.generated_assert_m0_6_local (stable_env (encoded_leaves s i ghost)).
Proof.
 unfold Tool.generated_assert_m0_6_local. intro enabled.
 apply (proj2 (assertion_6_predicate_integer s i ghost)).
 rewrite control_454_reference.
 apply reference_check_6; [exact checks|]. exact (assertion_6_guard_reference s i ghost enabled).
Qed.
Lemma reference_check_7 s i (checks : Reference.asserts s i)
 (enabled : Reference.v440 s i = 1) : Reference.v438 s i = 1.
Proof.
 unfold Reference.asserts in checks.
 have allchecks := (proj1 (@List.forallb_forall bool (fun b => b) (Reference.assertionChecks s i))) checks.
 have member : List.In (orb (negb (Z.eqb (Reference.v440 s i) 1)) (Z.eqb (Reference.v438 s i) 1)) (Reference.assertionChecks s i).
 { unfold Reference.assertionChecks. do 7 right. left; reflexivity. }
 have valid := allchecks _ member. rewrite enabled Z.eqb_refl in valid.
 cbn [negb orb] in valid. apply Z.eqb_eq. exact valid.
Qed.
Lemma assertion_7_guard_reference s i ghost
 (enabled : Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (445%nat))))) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (458%nat))))) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (463%nat))))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env (encoded_leaves s i ghost))) :
 Reference.v440 s i = 1.
Proof.
 apply (proj1 (assertion_7_guard_integers s i ghost)) in enabled.
 destruct enabled as [H445 [H458 H463]].
 rewrite leaf_445_integer in H445. change (OldBits.word 1 (Reference.r10_nhistoryValid s) = 1) in H445.
 rewrite control_458_reference in H458.
 rewrite control_463_reference in H463.
 unfold Reference.v440. rewrite H445 H458 H463. reflexivity.
Qed.
Lemma reference_assertion_7 s i ghost
 (checks : Reference.asserts s i) : Tool.generated_assert_m0_7_local (stable_env (encoded_leaves s i ghost)).
Proof.
 unfold Tool.generated_assert_m0_7_local. intro enabled.
 apply (proj2 (assertion_7_predicate_integer s i ghost)).
 rewrite control_461_reference.
 apply reference_check_7; [exact checks|]. exact (assertion_7_guard_reference s i ghost enabled).
Qed.
Lemma reference_check_8 s i (checks : Reference.asserts s i)
 (enabled : Reference.v440 s i = 1) : Reference.v443 s i = 1.
Proof.
 unfold Reference.asserts in checks.
 have allchecks := (proj1 (@List.forallb_forall bool (fun b => b) (Reference.assertionChecks s i))) checks.
 have member : List.In (orb (negb (Z.eqb (Reference.v440 s i) 1)) (Z.eqb (Reference.v443 s i) 1)) (Reference.assertionChecks s i).
 { unfold Reference.assertionChecks. do 8 right. left; reflexivity. }
 have valid := allchecks _ member. rewrite enabled Z.eqb_refl in valid.
 cbn [negb orb] in valid. apply Z.eqb_eq. exact valid.
Qed.
Lemma assertion_8_guard_reference s i ghost
 (enabled : Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (445%nat))))) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (458%nat))))) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (471%nat))))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env (encoded_leaves s i ghost))) :
 Reference.v440 s i = 1.
Proof.
 apply (proj1 (assertion_8_guard_integers s i ghost)) in enabled.
 destruct enabled as [H445 [H458 H471]].
 rewrite leaf_445_integer in H445. change (OldBits.word 1 (Reference.r10_nhistoryValid s) = 1) in H445.
 rewrite control_458_reference in H458.
 rewrite control_471_reference in H471.
 unfold Reference.v440. rewrite H445 H458 H471. reflexivity.
Qed.
Lemma reference_assertion_8 s i ghost
 (checks : Reference.asserts s i) : Tool.generated_assert_m0_8_local (stable_env (encoded_leaves s i ghost)).
Proof.
 unfold Tool.generated_assert_m0_8_local. intro enabled.
 apply (proj2 (assertion_8_predicate_integer s i ghost)).
 rewrite control_469_reference.
 apply reference_check_8; [exact checks|]. exact (assertion_8_guard_reference s i ghost enabled).
Qed.
Lemma reference_check_9 s i (checks : Reference.asserts s i)
 (enabled : Reference.v444 s i = 1) : Reference.v399 s i = 1.
Proof.
 unfold Reference.asserts in checks.
 have allchecks := (proj1 (@List.forallb_forall bool (fun b => b) (Reference.assertionChecks s i))) checks.
 have member : List.In (orb (negb (Z.eqb (Reference.v444 s i) 1)) (Z.eqb (Reference.v399 s i) 1)) (Reference.assertionChecks s i).
 { unfold Reference.assertionChecks. do 9 right. left; reflexivity. }
 have valid := allchecks _ member. rewrite enabled Z.eqb_refl in valid.
 cbn [negb orb] in valid. apply Z.eqb_eq. exact valid.
Qed.
Lemma assertion_9_guard_reference s i ghost
 (enabled : Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (475%nat))))) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (478%nat))))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env (encoded_leaves s i ghost))) :
 Reference.v444 s i = 1.
Proof.
 apply (proj1 (assertion_9_guard_integers s i ghost)) in enabled.
 destruct enabled as [H475 H478].
 rewrite leaf_475_integer in H475. change (OldBits.word 1 (Reference.r13_nwasStalled s) = 1) in H475.
 rewrite control_478_reference in H478.
 unfold Reference.v444. rewrite H475 H478. reflexivity.
Qed.
Lemma reference_assertion_9 s i ghost
 (checks : Reference.asserts s i) : Tool.generated_assert_m0_9_local (stable_env (encoded_leaves s i ghost)).
Proof.
 unfold Tool.generated_assert_m0_9_local. intro enabled.
 apply (proj2 (assertion_9_predicate_integer s i ghost)).
 rewrite control_8_reference.
 change (Reference.v399 s i = 1).
 apply reference_check_9; [exact checks|]. exact (assertion_9_guard_reference s i ghost enabled).
Qed.
Lemma reference_check_10 s i (checks : Reference.asserts s i)
 (enabled : Reference.v444 s i = 1) : Reference.v445 s i = 1.
Proof.
 unfold Reference.asserts in checks.
 have allchecks := (proj1 (@List.forallb_forall bool (fun b => b) (Reference.assertionChecks s i))) checks.
 have member : List.In (orb (negb (Z.eqb (Reference.v444 s i) 1)) (Z.eqb (Reference.v445 s i) 1)) (Reference.assertionChecks s i).
 { unfold Reference.assertionChecks. do 10 right. left; reflexivity. }
 have valid := allchecks _ member. rewrite enabled Z.eqb_refl in valid.
 cbn [negb orb] in valid. apply Z.eqb_eq. exact valid.
Qed.
Lemma assertion_10_guard_reference s i ghost
 (enabled : Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (475%nat))))) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (482%nat))))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env (encoded_leaves s i ghost))) :
 Reference.v444 s i = 1.
Proof.
 apply (proj1 (assertion_10_guard_integers s i ghost)) in enabled.
 destruct enabled as [H475 H482].
 rewrite leaf_475_integer in H475. change (OldBits.word 1 (Reference.r13_nwasStalled s) = 1) in H475.
 rewrite control_482_reference in H482.
 unfold Reference.v444. rewrite H475 H482. reflexivity.
Qed.
Lemma reference_assertion_10 s i ghost
 (checks : Reference.asserts s i) : Tool.generated_assert_m0_10_local (stable_env (encoded_leaves s i ghost)).
Proof.
 unfold Tool.generated_assert_m0_10_local. intro enabled.
 apply (proj2 (assertion_10_predicate_integer s i ghost)).
 rewrite output_480_reference.
 apply reference_check_10; [exact checks|]. exact (assertion_10_guard_reference s i ghost enabled).
Qed.
Print Assumptions reference_assertion_10.
