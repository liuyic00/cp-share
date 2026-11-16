#!/usr/bin/env python3
"""Transfer the actual generated assertion formulas using checked scalar lookup equality."""
from pathlib import Path
import re
P=Path(__file__).resolve().parent;raw=(P.parent/'Generated/Radix2Divider/Model.v').read_text()
s=['''From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import ScalarEvaluation ScalarExtensionality.
From Divider Require Import Model.
From Divider Require Import Model Stable SingleModule NodeProgress.
Module Tool := Divider.Model.
Local Open Scope N_scope.
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
''']
for id in range(11):
 m=re.search(r'Definition generated_assert_m0_'+str(id)+r'_local .*? := generated_expr_true (.*?) sem -> generated_expr_true (.*?) sem\.',raw);assert m,id;guard,pred=m.groups()
 for name,expr in [('guard',guard),('predicate',pred)]:
  s.append(f'''Lemma assertion_{id}_{name}_transfer env v
 (agree : forall dep, divider_domain dep -> VM.find dep env = VM.find dep (stable_env v)) :
 Tool.generated_expr_true {expr} env <-> Tool.generated_expr_true {expr} (stable_env v).
Proof. eapply generated_expr_transfer; [reflexivity| |exact agree].
 intros dep occurs. cbn [scalar_refs List.In] in occurs.
 repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity.
Qed.
''')
 s.append(f'''Lemma assertion_{id}_local_transfer env v
 (agree : forall dep, divider_domain dep -> VM.find dep env = VM.find dep (stable_env v)) :
 Tool.generated_assert_m0_{id}_local env <-> Tool.generated_assert_m0_{id}_local (stable_env v).
Proof.
 have G := assertion_{id}_guard_transfer env v agree.
 have P := assertion_{id}_predicate_transfer env v agree.
 unfold Tool.generated_assert_m0_{id}_local. tauto.
Qed.
Lemma assertion_{id}_instance states env (found : SVM.find [::] states = Some env) :
 Tool.generated_assert_m0_{id}_all states <-> Tool.generated_assert_m0_{id}_local env.
Proof.
 unfold Tool.generated_assert_m0_{id}_all. rewrite divider_instances_computed.
 change (((false = true) \\/ match SVM.find [::] states with Some sem => Tool.generated_assert_m0_{id}_local sem | None => False end) /\\ True <-> Tool.generated_assert_m0_{id}_local env).
 rewrite found. split; [intros [[bad|H] _]; [discriminate|exact H]|intro H; split; [right; exact H|exact I]].
Qed.
''')
s.append('Print Assumptions assertion_10_local_transfer.\nPrint Assumptions assertion_10_instance.\n')
(P/'AssertTransfer.v').write_text(''.join(s))
