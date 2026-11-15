#!/usr/bin/env python3
from pathlib import Path
import runpy
H=Path(__file__).resolve().parent
for mid in range(3):
 x=runpy.run_path(str(H/'stable_certificate.py'),init_globals={'MODULE_ID':mid,'OUTPUT_PREFIX':f'Child{mid}','WIDTH_LOG':f'small-child{mid}widths.log'})
 closure={k:{k} for k in x['leaves']};name=x['name'];out=['From Coq Require Import NArith.','From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.',f'From SmallMultiplier Require Import Child{mid}Stable.','Local Open Scope N_scope.']
 for k in x['ordered']:
  n=name(k);ds=x['refs'](x['nodes'][k]);closure[k]=set().union(*(closure[d] for d in ds))
  hs=' '.join(f'(H{j} : {name(d)} v = {name(d)} w)' for j,d in enumerate(ds))
  out +=[f'Lemma {n}_congr v w {hs} : {n} v = {n} w.',f'Proof. unfold {n}, closed_{n}. '+('rewrite '+' '.join(f'H{j}' for j in range(len(ds)))+'. ' if ds else '')+'reflexivity. Qed.']
  hs=' '.join(f'(I{j} : v {d[0]} {d[1]} = w {d[0]} {d[1]})' for j,d in enumerate(sorted(closure[k])))
  out +=[f'Lemma {n}_inputs v w {hs} : {n} v = {n} w.',f'Proof. apply {n}_congr.']
  for d in ds:
   if d in x['leaves']:out+=[' - assumption.']
   else:out +=[f' - apply {name(d)}_inputs; assumption.']
  out +=['Qed.']
 (H/f'Child{mid}Congruence.v').write_text('\n'.join(out)+'\n')
