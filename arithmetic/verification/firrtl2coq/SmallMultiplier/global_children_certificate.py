#!/usr/bin/env python3
from pathlib import Path
import json,runpy
H=Path(__file__).resolve().parent
g=json.loads((H/'global-dependencies.json').read_text());idx=json.loads((H/'global-key-index.json').read_text())
ctx={mid:runpy.run_path(str(H/'stable_certificate.py'),init_globals={'MODULE_ID':mid,'OUTPUT_PREFIX':f'Child{mid}','WIDTH_LOG':f'small-child{mid}widths.log'}) for mid in range(3)}
out=['From Coq Require Import NArith ZArith.','From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.','From nbits Require Import NBits.','From SmallMultiplier Require Import GlobalStable Child0Stable Child1Stable Child2Stable.','Local Open Scope N_scope.']
for ino,(p,mid) in enumerate(g['instances'].items()):
 if mid==3:continue
 x=ctx[mid];module=f'Child{mid}Stable'
 def key(k):return p+':'+str(k[1]) if k[0]==0 else p+':'+str(k[0])+':'+str(k[1])
 def gw(k):return 'global_word_'+str(idx[key(k)])
 out +=[f'Definition instance_{ino}_leaves (v:global_leaves) : {module}.leaf_values := fun scope id => match scope,id with']
 for k in sorted(x['leaves']):out +=[f'| {k[0]}, {k[1]} => {gw(k)} v']
 out+=['| _,_ => [::] end.']
 for k in sorted(x['leaves']):
  n=x['name'](k);out +=[f'Transparent {module}.{n} {gw(k)}.',f'Lemma instance_{ino}_{n} v : {module}.{n} (instance_{ino}_leaves v) = {gw(k)} v.',f'Proof. unfold {module}.{n}, instance_{ino}_leaves. reflexivity. Qed.',f'Opaque {module}.{n} {gw(k)}.']
 for k in x['ordered']:
  n=x['name'](k);num=idx[key(k)];ds=x['refs'](x['nodes'][k])
  out +=[f'Transparent {module}.{n} {gw(k)}.',f'Lemma instance_{ino}_{n} v : {module}.{n} (instance_{ino}_leaves v) = {gw(k)} v.',f'Proof. unfold {module}.{n}, {gw(k)}, {module}.closed_{n}, global_closed_{num}, {module}.expr_{n}, global_expr_{num}.']
  if ds:out+=[' rewrite '+' '.join(f'instance_{ino}_'+x['name'](d) for d in ds)+'.']
  out +=[f' reflexivity. Qed. Opaque {module}.{n} {gw(k)}.']
(H/'GlobalChildren.v').write_text('\n'.join(out)+'\n')
