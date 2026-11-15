#!/usr/bin/env python3
"""Emit syntactic node locations and checked topological dependency ranks."""
from pathlib import Path
import json,re
H=Path(__file__).resolve().parent
d=json.loads((H/'nodes.json').read_text()); leaf=set(d['registers']+d['inputs']); rank={n:0 for n in leaf}
for n in d['order']:
 deps=list(map(int,re.findall(r'\(@Eid VarOrder.T (\d+)\)',d['expressions'][str(n)])))
 rank[n]=1+max([rank[k] for k in deps],default=0)
s=['''From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import StatementFacts ScalarEvaluation ScalarExtensionality.
From Divider Require Import Model Stable.
Local Open Scope N_scope.
Fixpoint checked_node watched (stmts : @hfstmt_seq VarOrder.T) : option (@hfexpr VarOrder.T) :=
 match stmts with
 | Qnil => None
 | Qcons (Snode id rhs) rest =>
   if watched == id then if flat_sequence_frames watched rest then Some rhs else None
   else checked_node watched rest
 | Qcons stmt rest => if flat_statement stmt then checked_node watched rest else None
 end.
Lemma checked_node_sound watched stmts rhs :
 checked_node watched stmts = Some rhs -> node_certificate watched rhs stmts.
Proof.
 induction stmts as [|stmt rest IH]; cbn [checked_node]; try discriminate.
 destruct stmt as [|id t|id reg|id mem|id module_id|id expr|lhs expr|ref|cond yes no]; cbn [checked_node]; try (cbn [flat_statement]; discriminate); try solve [match goal with |- (if ?test then _ else _) = _ -> _ => destruct test eqn:F; try discriminate; intro E; apply node_certificate_later; [exact F|exact (IH E)] end].
 destruct (watched == id) eqn:same.
 - move/eqP: same => ->. destruct (flat_sequence_frames id rest) eqn:F; try discriminate.
   intro E; inversion E; subst. apply node_certificate_here. exact F.
 - intro E. apply node_certificate_later; [reflexivity|exact (IH E)].
Qed.
Definition dependency_rank (id : N) : nat := match id with
''']
for n in sorted(rank):s += [f'| {n} => {rank[n]}%nat']
s += ['| _ => 0%nat end.']
for n in d['order']:
 if n not in [2,8,9]:
  s += [f'Lemma node_{n}_certificate : node_certificate {n} expr_{n} generated_module_0_stmts_0.', 'Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.',f'Lemma node_{n}_not_register : registers_frame {n} generated_module_0_stmts_0 = true.', 'Proof. vm_compute. reflexivity. Qed.']
 s += [f'Lemma node_{n}_dependencies : forall id, List.In id (scalar_refs expr_{n}) -> (dependency_rank id < dependency_rank {n})%nat.',f'Proof. intros id found. cbn [expr_{n} scalar_refs List.In] in found. repeat destruct found as [found|found]; try contradiction; subst id; vm_compute; reflexivity. Qed.']
s+=['Print Assumptions node_483_certificate.','Print Assumptions node_483_dependencies.']
(H/'Certificates.v').write_text('\n'.join(s)+'\n');print('max rank',max(rank.values()))
