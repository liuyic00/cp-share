#!/usr/bin/env python3
"""Clock-independent combinational representation; no clock input constraint."""
from pathlib import Path
import json,re
P=Path(__file__).resolve().parent;j=json.loads((P/'nodes.json').read_text());leaves=sorted(j['inputs']+j['registers'])
s=['''From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths.
From Divider Require Import Stable Frames NodeProgress.
Local Open Scope N_scope.
Definition with_clock (v : leaf_values) (clock : seq bool) : leaf_values :=
 fun id => match id with 0 => clock | _ => v id end.
''']
for id in leaves:
 if id==0:continue
 s.append(f'''Transparent word_{id}.
Lemma word_{id}_clock v clock : word_{id} (with_clock v clock) = word_{id} v.
Proof. unfold word_{id}, with_clock. reflexivity. Qed.
Opaque word_{id}.
''')
for id in j['order']:
 deps=sorted(set(map(int,re.findall(r'Eid VarOrder.T (\d+)',j['expressions'][str(id)]))))
 assert 0 not in deps
 s.append(f'''Transparent word_{id}.
Lemma word_{id}_clock v clock : word_{id} (with_clock v clock) = word_{id} v.
Proof. unfold word_{id}, closed_{id}.
''')
 if deps:s.append(' rewrite '+ ' '.join(f'word_{dep}_clock' for dep in deps)+'.\n')
 s.append(f'reflexivity. Qed.\nOpaque word_{id}.\n')
s.append('''Lemma stable_clock_private v clock id
 (inside : divider_domain id) (nonclock : id <> 0) :
 VM.find id (stable_env (with_clock v clock)) = VM.find id (stable_env v).
Proof.
 apply divider_domain_cases in inside. unfold divider_ids in inside.
''')
for id in range(484):
 s.append(' destruct inside as [same|inside].\n')
 if id==0:s.append(' - subst id. contradiction.\n')
 else:s.append(f' - subst id. rewrite !target_{id}_value word_{id}_clock. reflexivity.\n')
s.append(' contradiction.\nQed.\nPrint Assumptions stable_clock_private.\n')
(P/'RuntimeRepresentation.v').write_text(''.join(s))
