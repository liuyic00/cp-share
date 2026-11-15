#!/usr/bin/env python3
"""Original hierarchical AST expression DAG certificates, indexed by paths."""
from pathlib import Path
import json,runpy
H=Path(__file__).resolve().parent
x=runpy.run_path(str(H/'stable_certificate.py'));g=json.loads((H/'global-dependencies.json').read_text())
widths={3:x['root_types']}
for mid in range(3):widths[mid]={int(i):tuple(t) for i,t in json.loads((H/f'Child{mid}stable-nodes.json').read_text())['root_types'].items()}
keys=g['leaves']+g['order'];idx={k:i for i,k in enumerate(keys)}
def parts(k):
 p,*r=k.split(':');return p,list(map(int,r))
def childpath(p,i):return p+'/'+str(i) if p else str(i)
def typeof(k):
 p,r=parts(k)
 if len(r)==1:return widths[g['instances'][p]][r[0]]
 mid=g['instances'][childpath(p,r[0])]
 return next((kind,w) for id,d,kind,w in x['ports'][mid] if id==r[1])
def typ(k):
 kind,w=typeof(k);return 'Fclock' if kind==2 else f'({"Fuint" if kind==0 else "Fsint"} {w})'
def word(k):return f'global_word_{idx[k]}'
def val(k):return f'(Gval {typ(k)} ({word(k)} v))'
def bundle(p,inst,fields):
 t='Bnil';mid=g['instances'][childpath(p,inst)]
 for pid,d,_,_ in reversed(x['ports'][mid]):
  if pid in fields:t=f'(Bflips {pid} {"Flipped" if d=="input" else "Nflip"} {val(p+":"+str(inst)+":"+str(pid))} {t})'
 return f'(Bval {t})'
def env(deps):
 groups={};p=''
 for k in deps:
  p,r=parts(k);groups.setdefault((0 if len(r)==1 else r[0]),[]).append(r[-1])
 e='(VM.empty hvalue)'
 for inst,ids in sorted(groups.items()):
  if inst==0:
   for id in ids:e=f'(VM.add {id} {val(p+":"+str(id))} {e})'
  else:e=f'(VM.add {inst} {bundle(p,inst,ids)} {e})'
 return e
out=['''From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model Stable Child0Stable Child1Stable Child2Stable.
Local Open Scope N_scope.
Definition global_leaves := nat -> bits.''']
for k in g['leaves']:out +=[f'Definition {word(k)} (v:global_leaves) := v {idx[k]}%nat.']
for k in g['order']:
 n=idx[k];node=g['nodes'][k]
 if node['kind'].startswith('sync'):out +=[f'Definition {word(k)} (v:global_leaves) := {word(node["deps"][0])} v.']
 else:
  out +=[f'Definition global_expr_{n} : @hfexpr VarOrder.T := {node["expr"]}.',f'Definition global_closed_{n} (v:global_leaves) := {env(node["deps"])}.',f'Definition {word(k)} (v:global_leaves) := Stable.word_of_eval (eval_hfexpr global_expr_{n} (global_closed_{n} v) (global_closed_{n} v)).']
out+=['Opaque '+' '.join(word(k) for k in keys)+'.']
for p,mid in g['instances'].items():
 name='root' if not p else p.replace('/','_');module='Stable' if mid==3 else f'Child{mid}Stable'
 out +=[f'Definition global_values_{name} (v:global_leaves) (id:N) : hvalue := match id with']
 for id,t in sorted(widths[mid].items()):
  value=bundle(p,id,[port for port,_,_,_ in x['ports'][g['instances'][childpath(p,id)]]]) if t[0]==9 else val(p+':'+str(id))
  out +=[f'| {id} => {value}']
 out +=['| _ => Needtobedefined (Gtyp (Fuint 0)) end.',f'Definition global_env_{name} v := {module}.stable_shape (global_values_{name} v).']
for k in g['order']:
 n=idx[k];node=g['nodes'][k];p,_=parts(k);name='root' if not p else p.replace('/','_')
 if node['kind'].startswith('sync'):
  out +=[f'Transparent {word(k)}. Lemma global_sync_{n} v : {word(k)} v = {word(node["deps"][0])} v. Proof. unfold {word(k)}. reflexivity. Qed. Opaque {word(k)}.']
 else:
  out +=[f'Transparent {word(k)}.',f'Lemma global_closed_{n}_value v : eval_hfexpr global_expr_{n} (global_closed_{n} v) (global_closed_{n} v) = Some (Gval {typ(k)} ({word(k)} v)).',f'Proof. unfold {word(k)}, global_closed_{n}, global_expr_{n}, Stable.word_of_eval. {x["base"]} Qed.',f'Opaque {word(k)}.',f'Lemma global_node_{n}_value v : eval_hfexpr global_expr_{n} (global_env_{name} v) (global_env_{name} v) = Some (Gval {typ(k)} ({word(k)} v)).',f'Proof. change (eval_hfexpr global_expr_{n} (global_closed_{n} v) (global_closed_{n} v) = Some (Gval {typ(k)} ({word(k)} v))). apply global_closed_{n}_value. Qed.']
(H/'GlobalStable.v').write_text('\n'.join(out)+'\n')
(H/'global-key-index.json').write_text(json.dumps(idx,indent=2)+'\n')
print('Generated',len(keys),'path-indexed values')
