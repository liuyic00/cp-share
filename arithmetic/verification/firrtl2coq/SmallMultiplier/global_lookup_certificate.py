#!/usr/bin/env python3
from pathlib import Path
import json
H=Path(__file__).resolve().parent
g=json.loads((H/'global-dependencies.json').read_text());idx=json.loads((H/'global-key-index.json').read_text())
meta={3:json.loads((H/'stable-nodes.json').read_text())}
for mid in range(3):meta[mid]=json.loads((H/f'Child{mid}stable-nodes.json').read_text())
ports=meta[3]['ports']
def ename(p):return 'global_env_'+('root' if not p else p.replace('/','_'))
def path(p):return '[::'+(';'.join(reversed(p.split('/'))) if p else '')+']'
def typ(k):
 p,*r=k.split(':');mid=g['instances'][p]
 if len(r)==1:kind,w=meta[mid]['root_types'][r[0]]
 else:
  child=p+'/'+r[0] if p else r[0];childmid=g['instances'][child]
  _,_,kind,w=next(item for item in ports[str(childmid)] if item[0]==int(r[1]))
 return 'Fclock' if kind==2 else f'({"Fuint" if kind==0 else "Fsint"} {w})'
out=['From Coq Require Import NArith.','From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.','From simplssrlib Require Import Types SsrOrder Var.','From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.','From SmallMultiplier Require Import GlobalStable.','Local Open Scope N_scope.']
for k,n in idx.items():
 p,*r=k.split(':');value=f'(Gval {typ(k)} (global_word_{n} v))'
 if len(r)==1:
  out +=[f'Lemma global_lookup_{n} v : VM.find {r[0]} ({ename(p)} v) = Some {value}. Proof. reflexivity. Qed.']
 else:
  ref=f'(@Esubfield VarOrder.T (@Eid VarOrder.T {r[0]}) {r[1]})'
  out +=[f'Lemma global_lookup_{n} v : eval_href {ref} ({ename(p)} v) ({ename(p)} v) = Some {value}. Proof. reflexivity. Qed.',f'Lemma global_field_type_{n} v : eval_type_of_ref {ref} ({ename(p)} v) = Some (Gtyp {typ(k)}). Proof. reflexivity. Qed.']
e='(SVM.empty (VM.t hvalue))'
for i,p in enumerate(g['instances']):e=f'(SVM.add {path(p)} (envs {i}%nat) {e})'
out +=[f'Definition global_circuit_shape (envs:nat -> VM.t hvalue) : SVM.t (VM.t hvalue) := Eval vm_compute in {e}.','Definition global_target v := global_circuit_shape (fun i => match i with']
for i,p in enumerate(g['instances']):out +=[f'| {i}%nat => {ename(p)} v']
out+=['| _ => VM.empty hvalue end).']
for i,p in enumerate(g['instances']):out +=[f'Lemma global_instance_{i} v : SVM.find {path(p)} (global_target v) = Some ({ename(p)} v). Proof. reflexivity. Qed.']
(H/'GlobalLookups.v').write_text('\n'.join(out)+'\n')
