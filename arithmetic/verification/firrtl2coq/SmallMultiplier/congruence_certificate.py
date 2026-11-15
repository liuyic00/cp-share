#!/usr/bin/env python3
from pathlib import Path
import runpy
H=Path(__file__).resolve().parent
ctx=runpy.run_path(str(H/'stable_certificate.py'))
ordered=ctx['ordered'];nodes=ctx['nodes'];refs=ctx['refs'];name=ctx['name'];leaves=ctx['leaves']
selected=[k for k in ordered if k[0]==0 and 37<=k[1]<=198]
lines=['''From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From SmallMultiplier Require Import Stable.
Local Open Scope N_scope.
''']
for k in selected:
 n=name(k);ds=refs(nodes[k]);hs=' '.join(f'(H{i} : {name(d)} v = {name(d)} w)' for i,d in enumerate(ds))
 lines += [f'Lemma {n}_congr v w {hs} : {n} v = {n} w.',f'Proof. unfold {n}, closed_{n}. '+('rewrite '+' '.join(f'H{i}' for i in range(len(ds)))+'. ' if ds else '')+'reflexivity. Qed.']
 lines += [f'Lemma {n}_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : {n} v = {n} w.',f'Proof. apply {n}_congr.']
 for d in ds:
  if d==(0,2):lines +=[' - exact Ha.']
  elif d==(0,3):lines +=[' - exact Hb.']
  else:
   assert d in selected,d
   lines +=[f' - apply {name(d)}_inputs; assumption.']
 lines +=['Qed.']
(H/'Congruence.v').write_text('\n'.join(lines)+'\n')
print(len(selected),'input extensionality certificates')
