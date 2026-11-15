#!/usr/bin/env python3
from pathlib import Path
import json,runpy
H=Path(__file__).resolve().parent
x=runpy.run_path(str(H/'stable_certificate.py'));idx=json.loads((H/'global-key-index.json').read_text())
def key(k):return ':'+str(k[1]) if k[0]==0 else ':'+str(k[0])+':'+str(k[1])
def gw(k):return 'global_word_'+str(idx[key(k)])
out=['From Coq Require Import NArith ZArith.','From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.','From nbits Require Import NBits.','From SmallMultiplier Require Import Stable GlobalStable FrontCheck Booth8.','Local Open Scope N_scope.','Definition top_global_leaves (v:global_leaves) : Stable.leaf_values := fun scope id => match scope,id with']
for k in sorted(x['leaves']):out += [f'| {k[0]}, {k[1]} => {gw(k)} v']
out +=['| _,_ => [::] end.']
for k in sorted(x['leaves']):
 n=x['name'](k);out +=[f'Transparent Stable.{n} {gw(k)}. Lemma top_{n} v : Stable.{n} (top_global_leaves v) = {gw(k)} v.',f'Proof. unfold Stable.{n}, top_global_leaves. reflexivity. Qed. Opaque Stable.{n} {gw(k)}.']
for k in x['ordered']:
 n=x['name'](k);num=idx[key(k)];ds=x['refs'](x['nodes'][k])
 out +=[f'Transparent Stable.{n} {gw(k)}. Lemma top_{n} v : Stable.{n} (top_global_leaves v) = {gw(k)} v.',f'Proof. unfold Stable.{n}, {gw(k)}, Stable.closed_{n}, global_closed_{num}, Stable.expr_{n}, global_expr_{num}.']
 if ds:out +=[' rewrite '+' '.join('top_'+x['name'](d) for d in ds)+'.']
 out +=[f' reflexivity. Qed. Opaque Stable.{n} {gw(k)}.']
i2=idx[':2'];i3=idx[':3']
expr=' + '.join(('' if c==1 else str(c)+'*')+f'to_Zpos (global_word_{idx[":"+str(n)]} v)' for n,c in [(71,1),(107,1),(144,4),(180,16),(198,64)])
out +=[f'''Theorem global_packed_product v a b
 (Ha : global_word_{i2} v = from_N 8 a) (Hb : global_word_{i3} v = from_N 8 b)
 (Hamin : N.lt a 256) (Hbmin : N.lt b 256) :
 Z.modulo ({expr}) 65536 =
 Z.modulo (Z.mul (signed8 (Z.of_N a)) (signed8 (Z.of_N b))) 65536.
Proof.
 rewrite - (top_word_71 v) - (top_word_107 v) - (top_word_144 v) - (top_word_180 v) - (top_word_198 v).
 exact (ast_front_product (top_global_leaves v) a b Ha Hb Hamin Hbmin).
Qed.
Print Assumptions global_packed_product.''']
(H/'GlobalTop.v').write_text('\n'.join(out)+'\n')
