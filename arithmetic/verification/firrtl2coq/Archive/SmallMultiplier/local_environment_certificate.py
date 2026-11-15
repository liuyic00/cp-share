#!/usr/bin/env python3
from pathlib import Path
import runpy
H=Path(__file__).resolve().parent
x=runpy.run_path(str(H/'stable_certificate.py'))
out=['From Coq Require Import NArith.','From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.','From simplssrlib Require Import Types SsrOrder Var.','From nbits Require Import NBits.','From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.','From SmallMultiplier Require Import Stable.','Local Open Scope N_scope.']
for k in x['ordered']:
 if k[0] or not 37<=k[1]<=198:continue
 n=x['name'](k);ds=x['refs'](x['nodes'][k]);t=x['typ'](k)
 out += [f'Lemma local_{n}_value v env']
 for j,d in enumerate(ds):out += [f' (H{j} : VM.find {d[1]} env = Some {x["value"](d)})']
 out += [f' : eval_hfexpr expr_{n} env env = Some (Gval {t} ({n} v)).',f'Proof. rewrite - (closed_{n}_value v). unfold expr_{n}, closed_{n}.'," cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].",' rewrite '+' '.join(f'?H{j}' for j in range(len(ds)))+'.' if ds else ''," repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].", ' rewrite '+' '.join(f'?H{j}' for j in range(len(ds)))+'.' if ds else '', " repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed."]
(H/'LocalEnvironment.v').write_text('\n'.join(out)+'\n')
