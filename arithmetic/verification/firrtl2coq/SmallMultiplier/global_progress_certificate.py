#!/usr/bin/env python3
"""Compose existing original-interpreter step certificates; no AST rewriting."""
from pathlib import Path
import json
H=Path(__file__).resolve().parent
g=json.loads((H/'global-dependencies.json').read_text());idx=json.loads((H/'global-key-index.json').read_text())
keys=sorted(idx,key=idx.get);meta=json.loads((H/'stable-nodes.json').read_text())
widths={3:meta['root_types']}
for m in range(3):widths[m]=json.loads((H/f'Child{m}stable-nodes.json').read_text())['root_types']
def parts(k):
 p,*r=k.split(':');return p,list(map(int,r))
def typ(k):
 p,r=parts(k)
 if len(r)==1:kind,w=widths[g['instances'][p]][str(r[0])]
 else:
  child=p+'/'+str(r[0]) if p else str(r[0]);m=g['instances'][child]
  _,_,kind,w=next(x for x in meta['ports'][str(m)] if x[0]==r[1])
 return ('Fclock' if kind==2 else f'({"Fuint" if kind==0 else "Fsint"} {w})'),w
def lookup(k,s):
 p,r=parts(k);path='[::'+';'.join(reversed(p.split('/')))+']' if p else '[::]'
 return f'circuit_lookup {path} {r[0]} {s}' if len(r)==1 else f'circuit_interface {path} {r[0]} {r[1]} {s}'
def val(k):return f'(Gval {typ(k)[0]} (global_word_{idx[k]} v))'
header='''From Coq Require Import NArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import HierarchyFacts PortFieldFacts.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalWidthFacts GlobalNodeSteps GlobalFieldSteps GlobalScalarSteps GlobalSyncSteps GlobalLeaves.
Local Open Scope N_scope.
'''
s=header
for name,result,func in [('global_value_at','option hvalue',lambda k:lookup(k,'states')),('global_target_at','hvalue',val),('global_type_at','fgtyp',lambda k:typ(k)[0]),('global_rank_at','nat',lambda k:str(g['ranks'][k])+'%nat'),('global_port_at','bool',lambda k:'true' if k in g['nodes'] and g['nodes'][k]['kind'] in ['portconnect','connect'] else 'false')]:
 args='(index:nat)'+(' states' if name=='global_value_at' else ' (v:global_leaves)' if name=='global_target_at' else '')
 default={'option hvalue':'None','hvalue':'Needtobedefined (Gtyp (Fuint 0))','fgtyp':'Fuint 0','nat':'0%nat','bool':'false'}[result]
 s+=f'Definition {name} {args} : {result} := match N.of_nat index with\n'
 s+='\n'.join(f'| {idx[k]} => {func(k)}' for k in keys)
 s+=f'\n| _ => {default} end.\n'
s+=f'''Definition global_ranked v level states := forall index, (index < {len(keys)})%coq_nat -> (global_rank_at index <= level)%coq_nat -> global_value_at index states = Some (global_target_at index v).
Definition global_port_types states := forall index, (index < {len(keys)})%coq_nat -> global_port_at index = true -> option_map type_of_val (global_value_at index states) = Some (Gtyp (global_type_at index)).
Lemma option_ground_value value ground (typed:option_map type_of_val value = Some (Gtyp ground)) : exists actual, value=Some actual /\ type_of_val actual=Gtyp ground.
Proof. destruct value; [eexists; split; [reflexivity|injection typed; tauto]|discriminate]. Qed.
'''
newtypes=s.replace(' GlobalNodeSteps GlobalFieldSteps GlobalScalarSteps GlobalSyncSteps GlobalLeaves','')
if (H/'GlobalProgressTypes.v').read_text()!=newtypes:(H/'GlobalProgressTypes.v').write_text(newtypes)
s=header+'From SmallMultiplier Require Import GlobalProgressTypes.\n'
chunks=[]
for k in keys:
 n=idx[k]
 if n and n%200==0:
  chunks.append(s);s=header+'From SmallMultiplier Require Import GlobalProgressTypes.\n'+f'From SmallMultiplier Require Export GlobalProgress{len(chunks)-1}.\n'
 kind=g['nodes'][k]['kind'] if k in g['nodes'] else 'leaf';r=g['ranks'][k];t,w=typ(k)
 if kind=='connect':
  d=g['nodes'][k]['deps'][0];dn=idx[d]
  s+=f'''Transparent global_word_{n}.
Lemma global_connect_{n}_alias v : global_word_{n} v = global_word_{dn} v.
Proof. unfold global_word_{n}, global_closed_{n}, global_expr_{n}, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_{n}.
'''
 s+=f'''Lemma global_progress_{n} invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:({r} <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 {lookup(k,'final')}=Some {val(k)}.
Proof.
'''
 if kind=='leaf':
  s+=f' eapply global_leaf_{n}_preserved; [exact (prior {n}%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia)))|reflexivity|exact ran].\n'
 else:
  ds=g['nodes'][k]['deps']
  if kind.startswith('sync'):
   d=ds[0];dn=idx[d]
   s+=f' apply (global_sync_{n}_link invalid snapshot final v); [eapply global_progress_{dn}; try eassumption; lia|exact ran].\n'
  else:
   if kind in ['connect','portconnect']:
    s+=f' have Typed := types {n}%nat (ltac:(lia)) (Logic.eq_refl true).\n'
    s+=f' destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].\n'
   label={'node':'node','connect':'scalar','portconnect':'field'}[kind]
   s+=f' eapply global_{label}_{n}_step.\n'
   for d in ds:s+=f' - exact (prior {idx[d]}%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change ({g["ranks"][d]} <= level)%coq_nat; lia))).\n'
   if kind in ['connect','portconnect']:
    s+=' - exact Initial.\n - exact TypedInitial.\n'
    if kind=='connect':s+=f' - rewrite global_connect_{n}_alias. apply adapt_uint_same. exact (global_size_{idx[ds[0]]} v sizes).\n'
    elif t=='Fclock':s+=' - reflexivity.\n'
    else:s+=f' - apply '+('adapt_uint_same' if t.startswith('(Fuint') else 'adapt_sint_same' if t.startswith('(Fsint') else 'ltac:(reflexivity)')+f'.'+(f' exact (global_size_{n} v sizes).' if t!='Fclock' else '')+'\n'
   s+=' - exact ran.\n'
 s+='Qed.\n'
chunks.append(s)
for chunk,body in enumerate(chunks):
 target=H/f'GlobalProgress{chunk}.v'
 if not target.exists() or target.read_text()!=body:target.write_text(body)
(H/'GlobalProgress.v').write_text(f'From SmallMultiplier Require Export GlobalProgress{len(chunks)-1}.\n')
print('Generated progress certificates for',len(keys),'original circuit values.')
