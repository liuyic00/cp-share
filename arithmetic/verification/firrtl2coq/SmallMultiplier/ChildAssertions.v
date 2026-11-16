From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import HierarchyFacts.
From SmallMultiplier Require Model.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalInstances GlobalProgressTypes GlobalChildWeights.
Module Tool:=SmallMultiplier.Model.
Local Open Scope N_scope.
Lemma assert_instances_from_members mid predicate states pairs
 (members:forall path,List.In (path,mid) pairs -> match SVM.find path states with Some env=>predicate env|None=>False end) :
 Tool.generated_assert_instances mid predicate states pairs.
Proof.
 induction pairs as [|[path actual] tail IH];[exact I|]. split.
 - destruct(actual==mid) eqn:Same.
   + move/eqP:Same=>Same. subst actual. right. apply members. left. reflexivity.
   + left. reflexivity.
 - apply IH. intros p Member. apply members. right. exact Member.
Qed.
Lemma child_assertion_1 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::7] states with Some env=>Tool.generated_assert_m0_0_local env|None=>False end.
Proof.
 have Known:=values 1379%nat (ltac:(lia)).
 change(circuit_lookup [::7] 15 states=Some(Gval(Fuint 1)(global_word_1379 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::7] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m0_0_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_1_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_2 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::8] states with Some env=>Tool.generated_assert_m0_0_local env|None=>False end.
Proof.
 have Known:=values 1394%nat (ltac:(lia)).
 change(circuit_lookup [::8] 15 states=Some(Gval(Fuint 1)(global_word_1394 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::8] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m0_0_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_2_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_3 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::9] states with Some env=>Tool.generated_assert_m1_1_local env|None=>False end.
Proof.
 have Known:=values 1412%nat (ltac:(lia)).
 change(circuit_lookup [::9] 19 states=Some(Gval(Fuint 1)(global_word_1412 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::9] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m1_1_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_3_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_4 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::10] states with Some env=>Tool.generated_assert_m1_1_local env|None=>False end.
Proof.
 have Known:=values 1430%nat (ltac:(lia)).
 change(circuit_lookup [::10] 19 states=Some(Gval(Fuint 1)(global_word_1430 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::10] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m1_1_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_4_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_5 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::11] states with Some env=>Tool.generated_assert_m2_2_local env|None=>False end.
Proof.
 have Known:=values 1458%nat (ltac:(lia)).
 change(circuit_lookup [::11] 34 states=Some(Gval(Fuint 1)(global_word_1458 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::11] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m2_2_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_5_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_6 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::10;11] states with Some env=>Tool.generated_assert_m1_1_local env|None=>False end.
Proof.
 have Known:=values 1480%nat (ltac:(lia)).
 change(circuit_lookup [::10;11] 19 states=Some(Gval(Fuint 1)(global_word_1480 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::10;11] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m1_1_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_6_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_7 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::11;11] states with Some env=>Tool.generated_assert_m1_1_local env|None=>False end.
Proof.
 have Known:=values 1498%nat (ltac:(lia)).
 change(circuit_lookup [::11;11] 19 states=Some(Gval(Fuint 1)(global_word_1498 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::11;11] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m1_1_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_7_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_8 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::12] states with Some env=>Tool.generated_assert_m2_2_local env|None=>False end.
Proof.
 have Known:=values 1526%nat (ltac:(lia)).
 change(circuit_lookup [::12] 34 states=Some(Gval(Fuint 1)(global_word_1526 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::12] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m2_2_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_8_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_9 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::10;12] states with Some env=>Tool.generated_assert_m1_1_local env|None=>False end.
Proof.
 have Known:=values 1548%nat (ltac:(lia)).
 change(circuit_lookup [::10;12] 19 states=Some(Gval(Fuint 1)(global_word_1548 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::10;12] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m1_1_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_9_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_10 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::11;12] states with Some env=>Tool.generated_assert_m1_1_local env|None=>False end.
Proof.
 have Known:=values 1566%nat (ltac:(lia)).
 change(circuit_lookup [::11;12] 19 states=Some(Gval(Fuint 1)(global_word_1566 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::11;12] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m1_1_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_10_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_11 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::13] states with Some env=>Tool.generated_assert_m2_2_local env|None=>False end.
Proof.
 have Known:=values 1594%nat (ltac:(lia)).
 change(circuit_lookup [::13] 34 states=Some(Gval(Fuint 1)(global_word_1594 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::13] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m2_2_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_11_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_12 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::10;13] states with Some env=>Tool.generated_assert_m1_1_local env|None=>False end.
Proof.
 have Known:=values 1616%nat (ltac:(lia)).
 change(circuit_lookup [::10;13] 19 states=Some(Gval(Fuint 1)(global_word_1616 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::10;13] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m1_1_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_12_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_13 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::11;13] states with Some env=>Tool.generated_assert_m1_1_local env|None=>False end.
Proof.
 have Known:=values 1634%nat (ltac:(lia)).
 change(circuit_lookup [::11;13] 19 states=Some(Gval(Fuint 1)(global_word_1634 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::11;13] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m1_1_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_13_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_14 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::14] states with Some env=>Tool.generated_assert_m2_2_local env|None=>False end.
Proof.
 have Known:=values 1662%nat (ltac:(lia)).
 change(circuit_lookup [::14] 34 states=Some(Gval(Fuint 1)(global_word_1662 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::14] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m2_2_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_14_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_15 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::10;14] states with Some env=>Tool.generated_assert_m1_1_local env|None=>False end.
Proof.
 have Known:=values 1684%nat (ltac:(lia)).
 change(circuit_lookup [::10;14] 19 states=Some(Gval(Fuint 1)(global_word_1684 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::10;14] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m1_1_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_15_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_16 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::11;14] states with Some env=>Tool.generated_assert_m1_1_local env|None=>False end.
Proof.
 have Known:=values 1702%nat (ltac:(lia)).
 change(circuit_lookup [::11;14] 19 states=Some(Gval(Fuint 1)(global_word_1702 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::11;14] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m1_1_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_16_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_17 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::15] states with Some env=>Tool.generated_assert_m2_2_local env|None=>False end.
Proof.
 have Known:=values 1730%nat (ltac:(lia)).
 change(circuit_lookup [::15] 34 states=Some(Gval(Fuint 1)(global_word_1730 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::15] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m2_2_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_17_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_18 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::10;15] states with Some env=>Tool.generated_assert_m1_1_local env|None=>False end.
Proof.
 have Known:=values 1752%nat (ltac:(lia)).
 change(circuit_lookup [::10;15] 19 states=Some(Gval(Fuint 1)(global_word_1752 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::10;15] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m1_1_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_18_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_19 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::11;15] states with Some env=>Tool.generated_assert_m1_1_local env|None=>False end.
Proof.
 have Known:=values 1770%nat (ltac:(lia)).
 change(circuit_lookup [::11;15] 19 states=Some(Gval(Fuint 1)(global_word_1770 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::11;15] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m1_1_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_19_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_20 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::16] states with Some env=>Tool.generated_assert_m2_2_local env|None=>False end.
Proof.
 have Known:=values 1798%nat (ltac:(lia)).
 change(circuit_lookup [::16] 34 states=Some(Gval(Fuint 1)(global_word_1798 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::16] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m2_2_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_20_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_21 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::10;16] states with Some env=>Tool.generated_assert_m1_1_local env|None=>False end.
Proof.
 have Known:=values 1820%nat (ltac:(lia)).
 change(circuit_lookup [::10;16] 19 states=Some(Gval(Fuint 1)(global_word_1820 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::10;16] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m1_1_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_21_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_22 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::11;16] states with Some env=>Tool.generated_assert_m1_1_local env|None=>False end.
Proof.
 have Known:=values 1838%nat (ltac:(lia)).
 change(circuit_lookup [::11;16] 19 states=Some(Gval(Fuint 1)(global_word_1838 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::11;16] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m1_1_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_22_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_23 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::17] states with Some env=>Tool.generated_assert_m2_2_local env|None=>False end.
Proof.
 have Known:=values 1866%nat (ltac:(lia)).
 change(circuit_lookup [::17] 34 states=Some(Gval(Fuint 1)(global_word_1866 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::17] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m2_2_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_23_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_24 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::10;17] states with Some env=>Tool.generated_assert_m1_1_local env|None=>False end.
Proof.
 have Known:=values 1888%nat (ltac:(lia)).
 change(circuit_lookup [::10;17] 19 states=Some(Gval(Fuint 1)(global_word_1888 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::10;17] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m1_1_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_24_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_25 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::11;17] states with Some env=>Tool.generated_assert_m1_1_local env|None=>False end.
Proof.
 have Known:=values 1906%nat (ltac:(lia)).
 change(circuit_lookup [::11;17] 19 states=Some(Gval(Fuint 1)(global_word_1906 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::11;17] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m1_1_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_25_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_26 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::18] states with Some env=>Tool.generated_assert_m2_2_local env|None=>False end.
Proof.
 have Known:=values 1934%nat (ltac:(lia)).
 change(circuit_lookup [::18] 34 states=Some(Gval(Fuint 1)(global_word_1934 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::18] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m2_2_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_26_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_27 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::10;18] states with Some env=>Tool.generated_assert_m1_1_local env|None=>False end.
Proof.
 have Known:=values 1956%nat (ltac:(lia)).
 change(circuit_lookup [::10;18] 19 states=Some(Gval(Fuint 1)(global_word_1956 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::10;18] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m1_1_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_27_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_28 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::11;18] states with Some env=>Tool.generated_assert_m1_1_local env|None=>False end.
Proof.
 have Known:=values 1974%nat (ltac:(lia)).
 change(circuit_lookup [::11;18] 19 states=Some(Gval(Fuint 1)(global_word_1974 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::11;18] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m1_1_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_28_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_29 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::19] states with Some env=>Tool.generated_assert_m1_1_local env|None=>False end.
Proof.
 have Known:=values 1992%nat (ltac:(lia)).
 change(circuit_lookup [::19] 19 states=Some(Gval(Fuint 1)(global_word_1992 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::19] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m1_1_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_29_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_30 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::20] states with Some env=>Tool.generated_assert_m0_0_local env|None=>False end.
Proof.
 have Known:=values 2007%nat (ltac:(lia)).
 change(circuit_lookup [::20] 15 states=Some(Gval(Fuint 1)(global_word_2007 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::20] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m0_0_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_30_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_31 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::21] states with Some env=>Tool.generated_assert_m0_0_local env|None=>False end.
Proof.
 have Known:=values 2022%nat (ltac:(lia)).
 change(circuit_lookup [::21] 15 states=Some(Gval(Fuint 1)(global_word_2022 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::21] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m0_0_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_31_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_32 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::22] states with Some env=>Tool.generated_assert_m0_0_local env|None=>False end.
Proof.
 have Known:=values 2037%nat (ltac:(lia)).
 change(circuit_lookup [::22] 15 states=Some(Gval(Fuint 1)(global_word_2037 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::22] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m0_0_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_32_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_33 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::23] states with Some env=>Tool.generated_assert_m0_0_local env|None=>False end.
Proof.
 have Known:=values 2052%nat (ltac:(lia)).
 change(circuit_lookup [::23] 15 states=Some(Gval(Fuint 1)(global_word_2052 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::23] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m0_0_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_33_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_34 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::24] states with Some env=>Tool.generated_assert_m0_0_local env|None=>False end.
Proof.
 have Known:=values 2067%nat (ltac:(lia)).
 change(circuit_lookup [::24] 15 states=Some(Gval(Fuint 1)(global_word_2067 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::24] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m0_0_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_34_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_35 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::25] states with Some env=>Tool.generated_assert_m0_0_local env|None=>False end.
Proof.
 have Known:=values 2082%nat (ltac:(lia)).
 change(circuit_lookup [::25] 15 states=Some(Gval(Fuint 1)(global_word_2082 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::25] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m0_0_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_35_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_36 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::26] states with Some env=>Tool.generated_assert_m0_0_local env|None=>False end.
Proof.
 have Known:=values 2097%nat (ltac:(lia)).
 change(circuit_lookup [::26] 15 states=Some(Gval(Fuint 1)(global_word_2097 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::26] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m0_0_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_36_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_37 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::27] states with Some env=>Tool.generated_assert_m1_1_local env|None=>False end.
Proof.
 have Known:=values 2115%nat (ltac:(lia)).
 change(circuit_lookup [::27] 19 states=Some(Gval(Fuint 1)(global_word_2115 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::27] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m1_1_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_37_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_38 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::28] states with Some env=>Tool.generated_assert_m1_1_local env|None=>False end.
Proof.
 have Known:=values 2133%nat (ltac:(lia)).
 change(circuit_lookup [::28] 19 states=Some(Gval(Fuint 1)(global_word_2133 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::28] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m1_1_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_38_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_39 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::29] states with Some env=>Tool.generated_assert_m0_0_local env|None=>False end.
Proof.
 have Known:=values 2148%nat (ltac:(lia)).
 change(circuit_lookup [::29] 15 states=Some(Gval(Fuint 1)(global_word_2148 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::29] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m0_0_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_39_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_40 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::30] states with Some env=>Tool.generated_assert_m0_0_local env|None=>False end.
Proof.
 have Known:=values 2163%nat (ltac:(lia)).
 change(circuit_lookup [::30] 15 states=Some(Gval(Fuint 1)(global_word_2163 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::30] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m0_0_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_40_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_41 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::31] states with Some env=>Tool.generated_assert_m0_0_local env|None=>False end.
Proof.
 have Known:=values 2178%nat (ltac:(lia)).
 change(circuit_lookup [::31] 15 states=Some(Gval(Fuint 1)(global_word_2178 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::31] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m0_0_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_41_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_42 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::32] states with Some env=>Tool.generated_assert_m0_0_local env|None=>False end.
Proof.
 have Known:=values 2193%nat (ltac:(lia)).
 change(circuit_lookup [::32] 15 states=Some(Gval(Fuint 1)(global_word_2193 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::32] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m0_0_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_42_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_43 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::33] states with Some env=>Tool.generated_assert_m1_1_local env|None=>False end.
Proof.
 have Known:=values 2211%nat (ltac:(lia)).
 change(circuit_lookup [::33] 19 states=Some(Gval(Fuint 1)(global_word_2211 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::33] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m1_1_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_43_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_44 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::34] states with Some env=>Tool.generated_assert_m0_0_local env|None=>False end.
Proof.
 have Known:=values 2226%nat (ltac:(lia)).
 change(circuit_lookup [::34] 15 states=Some(Gval(Fuint 1)(global_word_2226 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::34] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m0_0_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_44_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_45 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::35] states with Some env=>Tool.generated_assert_m0_0_local env|None=>False end.
Proof.
 have Known:=values 2241%nat (ltac:(lia)).
 change(circuit_lookup [::35] 15 states=Some(Gval(Fuint 1)(global_word_2241 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::35] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m0_0_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_45_assert v sizes). reflexivity.
Qed.
Lemma child_assertion_46 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find [::36] states with Some env=>Tool.generated_assert_m0_0_local env|None=>False end.
Proof.
 have Known:=values 2256%nat (ltac:(lia)).
 change(circuit_lookup [::36] 15 states=Some(Gval(Fuint 1)(global_word_2256 v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find [::36] states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m0_0_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_46_assert v sizes). reflexivity.
Qed.
Theorem all_child_assertions_0 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 Tool.generated_assert_m0_0_all states.
Proof.
 unfold Tool.generated_assert_m0_0_all.
 change (match find_circuit_instances Model.generated_modules Model.generated_top with Some im=>Tool.generated_assert_instances 0 Tool.generated_assert_m0_0_local states (SVM.elements im)|None=>False end).
 rewrite multiplier_instances_correct. apply assert_instances_from_members.
 intros path Member.
 let pairs:=eval vm_compute in (SVM.elements multiplier_instances) in change(List.In (path,0) pairs) in Member.
 cbn [List.In] in Member.
 repeat match goal with H:_ \/ _ |- _ => destruct H as [H|H] end; try contradiction;
 inversion Member; subst; clear Member;
 first [exact(child_assertion_1 v states sizes values)|exact(child_assertion_2 v states sizes values)|exact(child_assertion_30 v states sizes values)|exact(child_assertion_31 v states sizes values)|exact(child_assertion_32 v states sizes values)|exact(child_assertion_33 v states sizes values)|exact(child_assertion_34 v states sizes values)|exact(child_assertion_35 v states sizes values)|exact(child_assertion_36 v states sizes values)|exact(child_assertion_39 v states sizes values)|exact(child_assertion_40 v states sizes values)|exact(child_assertion_41 v states sizes values)|exact(child_assertion_42 v states sizes values)|exact(child_assertion_44 v states sizes values)|exact(child_assertion_45 v states sizes values)|exact(child_assertion_46 v states sizes values)].
Qed.
Theorem all_child_assertions_1 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 Tool.generated_assert_m1_1_all states.
Proof.
 unfold Tool.generated_assert_m1_1_all.
 change (match find_circuit_instances Model.generated_modules Model.generated_top with Some im=>Tool.generated_assert_instances 1 Tool.generated_assert_m1_1_local states (SVM.elements im)|None=>False end).
 rewrite multiplier_instances_correct. apply assert_instances_from_members.
 intros path Member.
 let pairs:=eval vm_compute in (SVM.elements multiplier_instances) in change(List.In (path,1) pairs) in Member.
 cbn [List.In] in Member.
 repeat match goal with H:_ \/ _ |- _ => destruct H as [H|H] end; try contradiction;
 inversion Member; subst; clear Member;
 first [exact(child_assertion_3 v states sizes values)|exact(child_assertion_4 v states sizes values)|exact(child_assertion_6 v states sizes values)|exact(child_assertion_7 v states sizes values)|exact(child_assertion_9 v states sizes values)|exact(child_assertion_10 v states sizes values)|exact(child_assertion_12 v states sizes values)|exact(child_assertion_13 v states sizes values)|exact(child_assertion_15 v states sizes values)|exact(child_assertion_16 v states sizes values)|exact(child_assertion_18 v states sizes values)|exact(child_assertion_19 v states sizes values)|exact(child_assertion_21 v states sizes values)|exact(child_assertion_22 v states sizes values)|exact(child_assertion_24 v states sizes values)|exact(child_assertion_25 v states sizes values)|exact(child_assertion_27 v states sizes values)|exact(child_assertion_28 v states sizes values)|exact(child_assertion_29 v states sizes values)|exact(child_assertion_37 v states sizes values)|exact(child_assertion_38 v states sizes values)|exact(child_assertion_43 v states sizes values)].
Qed.
Theorem all_child_assertions_2 v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 Tool.generated_assert_m2_2_all states.
Proof.
 unfold Tool.generated_assert_m2_2_all.
 change (match find_circuit_instances Model.generated_modules Model.generated_top with Some im=>Tool.generated_assert_instances 2 Tool.generated_assert_m2_2_local states (SVM.elements im)|None=>False end).
 rewrite multiplier_instances_correct. apply assert_instances_from_members.
 intros path Member.
 let pairs:=eval vm_compute in (SVM.elements multiplier_instances) in change(List.In (path,2) pairs) in Member.
 cbn [List.In] in Member.
 repeat match goal with H:_ \/ _ |- _ => destruct H as [H|H] end; try contradiction;
 inversion Member; subst; clear Member;
 first [exact(child_assertion_5 v states sizes values)|exact(child_assertion_8 v states sizes values)|exact(child_assertion_11 v states sizes values)|exact(child_assertion_14 v states sizes values)|exact(child_assertion_17 v states sizes values)|exact(child_assertion_20 v states sizes values)|exact(child_assertion_23 v states sizes values)|exact(child_assertion_26 v states sizes values)].
Qed.
