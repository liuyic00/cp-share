from pathlib import Path
import json
H=Path(__file__).resolve().parent
g=json.loads((H/'global-dependencies.json').read_text());idx=json.loads((H/'global-key-index.json').read_text())
s=r'''From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import HierarchyFacts.
From ArithmeticFIRRTL Require ArrayMulDataModule8.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalInstances GlobalProgressTypes GlobalChildWeights.
Module Tool:=ArithmeticFIRRTL.ArrayMulDataModule8.
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
'''
for num,(path,mid) in enumerate(g['instances'].items()):
 if mid==3:continue
 pred=[15,19,34][mid];n=idx[path+':'+str(pred)];p='[::'+';'.join(reversed(path.split('/')))+']'
 s+=f'''Lemma child_assertion_{num} v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 match SVM.find {p} states with Some env=>Tool.generated_assert_m{mid}_{mid}_local env|None=>False end.
Proof.
 have Known:=values {n}%nat (ltac:(lia)).
 change(circuit_lookup {p} {pred} states=Some(Gval(Fuint 1)(global_word_{n} v))) in Known.
 unfold circuit_lookup in Known.
 destruct(SVM.find {p} states) as [env|] eqn:Found;[|discriminate].
 unfold Tool.generated_assert_m{mid}_{mid}_local. intros Guard.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite Known (instance_{num}_assert v sizes). reflexivity.
Qed.
'''
for mid in range(3):
 s+=f'''Theorem all_child_assertions_{mid} v states
 (sizes:global_leaf_sizes v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)) :
 Tool.generated_assert_m{mid}_{mid}_all states.
Proof.
 unfold Tool.generated_assert_m{mid}_{mid}_all.
 change (match find_circuit_instances Model.generated_modules Model.generated_top with Some im=>Tool.generated_assert_instances {mid} Tool.generated_assert_m{mid}_{mid}_local states (SVM.elements im)|None=>False end).
 rewrite multiplier_instances_correct. apply assert_instances_from_members.
 intros path Member.
 let pairs:=eval vm_compute in (SVM.elements multiplier_instances) in change(List.In (path,{mid}) pairs) in Member.
 cbn [List.In] in Member.
 repeat match goal with H:_ \\/ _ |- _ => destruct H as [H|H] end; try contradiction;
 inversion Member; subst; clear Member;
 first ['''+'|'.join(f'exact(child_assertion_{num} v states sizes values)' for num,(p,m) in enumerate(g['instances'].items()) if m==mid)+'''].
Qed.
'''
(H/'ChildAssertions.v').write_text(s)
