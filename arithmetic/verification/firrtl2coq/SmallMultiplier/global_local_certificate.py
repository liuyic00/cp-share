#!/usr/bin/env python3
from pathlib import Path
import runpy
H=Path(__file__).resolve().parent
x=runpy.run_path(str(H/'global_stable_certificate.py'));g=x['g'];idx=x['idx'];typ=x['typ'];word=x['word'];val=x['val'];parts=x['parts']
out=['From Coq Require Import NArith.','From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.','From simplssrlib Require Import Types SsrOrder Var.','From nbits Require Import NBits.','From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.','From SmallMultiplier Require Import GlobalStable.','Local Open Scope N_scope.']
for k in g['order']:
 node=g['nodes'][k]
 if node['kind'].startswith('sync'):continue
 n=idx[k];ds=node['deps'];out +=[f'Lemma global_local_{n} v env']
 for j,d in enumerate(ds):
  p,r=parts(d);read=f'VM.find {r[0]} env' if len(r)==1 else f'eval_href (@Esubfield VarOrder.T (@Eid VarOrder.T {r[0]}) {r[1]}) env env'
  out +=[f' (H{j} : {read} = Some {val(d)})']
 out +=[f' : eval_hfexpr global_expr_{n} env env = Some (Gval {typ(k)} ({word(k)} v)).',f'Proof. rewrite - (global_closed_{n}_value v). unfold global_expr_{n}, global_closed_{n}.'," cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref]."]
 ps=[j for j,d in enumerate(ds) if len(parts(d)[1])==2]
 if ps:out+=[' rewrite '+' '.join(f'?H{j}' for j in ps)+'.']
 out+=[' cbn [eval_href].']
 if ds:out+=[' rewrite '+' '.join(f'?H{j}' for j in range(len(ds)))+'.']
 out +=[" repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr']."]
 if ds:out+=[' rewrite '+' '.join(f'?H{j}' for j in range(len(ds)))+'.']
 out +=[" repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed."]
(H/'GlobalLocal.v').write_text('\n'.join(out)+'\n')
