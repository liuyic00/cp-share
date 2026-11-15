#!/usr/bin/env python3
"""Generate checked local type certificates, without the upstream admitted theorem."""
from pathlib import Path
import json,re
H=Path(__file__).resolve().parent
d=json.loads((H/'nodes.json').read_text()); widths={int(k):v for k,v in d['widths'].items()}; leaf=set(d['inputs']+d['registers'])
s=['''From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths.
From ArithmeticCommon Require Import EnvironmentFacts ScalarEvaluation ScalarTyping.
From Divider Require Import Stable Representation.
Local Open Scope N_scope.
Section TypedLeaves.
Variable v : leaf_values.
''']
for n in sorted(leaf):
 s += [f'Hypothesis leaf_{n}_size : size (v {n}) = {widths[n]}%nat.',f'Lemma word_{n}_size : size (word_{n} v) = {widths[n]}%nat.', f'Proof. Transparent word_{n}. unfold word_{n}. exact leaf_{n}_size. Qed.', f'Opaque word_{n}.']
for n in d['order']:
 deps=sorted(set(map(int,re.findall(r'\(@Eid VarOrder.T (\d+)\)',d['expressions'][str(n)]))))
 s += [f'Lemma closed_{n}_typed : env_typed (closed_{n} v).',f'Proof. unfold closed_{n}.']
 # closed maps ascending insertion: determine traversal order from definition
 text=(H/'Stable.v').read_text(); body=re.search(rf'Definition closed_{n} .*? := (.*)\.',text).group(1)
 keys=list(map(int,re.findall(r'VM.add (\d+)',body)))
 def proof(keys):
  if not keys:return 'apply env_typed_empty.'
  k=keys[0]
  return f'apply env_typed_add_uint.\n' + '{ '+proof(keys[1:])+' }\n'+f'exact word_{k}_size.'
 s += [proof(keys),'Qed.',f'Lemma word_{n}_size : size (word_{n} v) = {widths[n]}%nat.', 'Proof.',f' apply (scalar_eval_uint_size (closed_{n} v) (closed_{n} v) expr_{n} {widths[n]} {widths[n]} (word_{n} v)).',f' - exact closed_{n}_typed.',f' - unfold expr_{n}. reflexivity.',f' - exact (closed_{n}_value v).',f' - unfold expr_{n}, closed_{n}. reflexivity.','Qed.']
env='(VM.empty hvalue)'
for n in sorted(widths):
 ty='Fclock' if n==0 else f'(Fuint {widths[n]})'
 env=f'(VM.add {n} (Gval {ty} (word_{n} v)) {env})'
s += ['Lemma stable_env_typed : env_typed (stable_env v).','Proof.',f' change (env_typed {env}).']
for n in reversed(sorted(widths)):
 ty='clock' if n==0 else 'uint'
 s += [f' apply env_typed_add_{ty}; [|exact word_{n}_size].']
s+=[' apply env_typed_empty.','Qed.','End TypedLeaves.', 'Print Assumptions word_483_size.', 'Print Assumptions stable_env_typed.']
for n in sorted(widths):
 s += [f'Lemma encoded_word_{n}_size s i ghost : size (word_{n} (encoded_leaves s i ghost)) = {widths[n]}%nat.', f'Proof. apply word_{n}_size; apply BitvectorFacts.encode_size. Qed.']
s += ['Lemma encoded_stable_env_typed s i ghost : env_typed (stable_env (encoded_leaves s i ghost)).', 'Proof. apply stable_env_typed; apply BitvectorFacts.encode_size. Qed.']
(H/'Typing.v').write_text('\n'.join(s)+'\n')
print('Typed node certificates:',len(d['order']))
