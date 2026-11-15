#!/usr/bin/env python3
from pathlib import Path
import re,runpy
H=Path(__file__).resolve().parent
model=(H/'Model.v').read_text()
for mid in range(3):
 x=runpy.run_path(str(H/'stable_certificate.py'),init_globals={'MODULE_ID':mid,'OUTPUT_PREFIX':f'Child{mid}','WIDTH_LOG':f'small-child{mid}widths.log'})
 out=['From Coq Require Import NArith.','From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.','From simplssrlib Require Import Types SsrOrder Var.','From nbits Require Import NBits.','From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.','From ArithmeticCommon Require Import StatementFacts ScalarEvaluation.',f'From SmallMultiplier Require Import Model NodeCertificateCheck Child{mid}Stable Child{mid}Local.','Local Open Scope N_scope.']
 body=model.split(f'Definition generated_module_{mid}_stmts_0')[1].split(f'Definition generated_module_{mid} :')[0]
 ids=list(map(int,re.findall(r'\(@Snode VarOrder.T (\d+)',body)))
 for n in ids:
  k=(0,n);ds=x['refs'](x['nodes'][k]);t=x['typ'](k)
  out +=[f'Lemma node_{n}_certificate : node_certificate {n} expr_word_{n} generated_module_{mid}_stmts_0.', 'Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.',f'Lemma pass_word_{n} invalid v old before after']
  for j,d in enumerate(ds):
   read=f'VM.find {d[1]} old' if d[0]==0 else f'eval_href (@Esubfield VarOrder.T (@Eid VarOrder.T {d[0]}) {d[1]}) old old'
   out +=[f' (H{j} : {read} = Some {x["value"](d)})']
  out +=[f' (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_{mid}_stmts_0 = Some after) :',f' VM.find {n} after = Some (Gval {t} (word_{n} v)).',f'Proof. eapply pass_node_value; [exact node_{n}_certificate|vm_compute;reflexivity| |exact ran].']
  if any(d[0] for d in ds):out +=[f' change (eval_hfexpr expr_word_{n} old old = Some (Gval {t} (word_{n} v))).']
  else:out+=[' rewrite scalar_eval_memory_irrelevant; [|reflexivity].']
  out +=[f' apply local_word_{n}_value; assumption. Qed.']
 (H/f'Child{mid}Pass.v').write_text('\n'.join(out)+'\n')
