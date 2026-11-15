#!/usr/bin/env python3
from pathlib import Path
import runpy
H=Path(__file__).resolve().parent
for mid in range(3):
 x=runpy.run_path(str(H/'stable_certificate.py'),init_globals={'MODULE_ID':mid,'OUTPUT_PREFIX':f'Child{mid}','WIDTH_LOG':f'small-child{mid}widths.log'})
 out=['From Coq Require Import NArith.','From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.','From simplssrlib Require Import Types SsrOrder Var.','From nbits Require Import NBits.','From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.',f'From SmallMultiplier Require Import Child{mid}Stable.','Local Open Scope N_scope.']
 for k in x['ordered']:
  n=x['name'](k);ds=x['refs'](x['nodes'][k]);t=x['typ'](k)
  out += [f'Lemma local_{n}_value v env']
  for j,d in enumerate(ds):
   read=f'VM.find {d[1]} env' if d[0]==0 else f'eval_href (@Esubfield VarOrder.T (@Eid VarOrder.T {d[0]}) {d[1]}) env env'
   out +=[f' (H{j} : {read} = Some {x["value"](d)})']
  out += [f' : eval_hfexpr expr_{n} env env = Some (Gval {t} ({n} v)).',f'Proof. rewrite - (closed_{n}_value v). unfold expr_{n}, closed_{n}.'," cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref]."]
  if any(d[0] for d in ds):out+=[' rewrite '+' '.join(f'?H{j}' for j,d in enumerate(ds) if d[0])+'.']
  out +=[" cbn [eval_href]."]
  out += [' rewrite '+' '.join(f'?H{j}' for j in range(len(ds)))+'.' if ds else ''," repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].", ' rewrite '+' '.join(f'?H{j}' for j in range(len(ds)))+'.' if ds else '', " repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed."]
 (H/f'Child{mid}Local.v').write_text('\n'.join(out)+'\n')
