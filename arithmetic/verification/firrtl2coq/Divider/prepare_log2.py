#!/usr/bin/env python3
from pathlib import Path
import json,re
H=Path(__file__).resolve().parent;d=json.loads((H/'nodes.json').read_text());m=json.loads((H/'node-matches.json').read_text())
old=(H.parents[1]/'rocq/Generated/Radix2Divider.v').read_text()
defs={int(k):v for k,v in re.findall(r'Definition v(\d+) .*? := (.*)\.',old)}
known={14:('node14_reference',1),68:('mux_68_reference',81)}
for f,prefix in [('Slices.v','slice'),('Reductions.v','reduction')]:
 for n,o in re.findall(r'Lemma '+prefix+r'_(\d+)_reference .*?= Reference.v(\d+) s i\.',(H/f).read_text()):known[int(n)]=(f'{prefix}_{n}_reference',int(o))
s=['''From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From ArithmeticCommon Require Import BitvectorFacts.
From Divider Require Import Stable Representation Typing ReferenceNodes Slices Reductions Muxes MuxShapes Concats.
Local Open Scope Z_scope.
'''];count=0
for n in d['order']:
 if n in known or str(n) not in m:continue
 expr=d['expressions'][str(n)]
 op='mux' if expr.startswith('(@Emux') else 'concat' if expr.startswith('(@Eprim_binop VarOrder.T Bcat') else None
 if not op:continue
 deps=sorted(set(map(int,re.findall(r'Eid VarOrder.T (\d+)',expr))))
 if not all(k in known for k in deps):continue
 oldid=m[str(n)][0];w=d['widths'][str(n)];stop={v[1] for v in known.values()};unfold=[]
 def visit(k):
  if k in stop or k in unfold:return
  unfold.append(k)
  for dep in map(int,re.findall(r'\bv(\d+) s i',defs[k])):visit(dep)
 visit(oldid)
 if oldid not in unfold:continue
 s += [f'Lemma log2_{n}_reference s i ghost : to_Zpos (word_{n} (encoded_leaves s i ghost)) = Reference.v{oldid} s i.', 'Proof.']
 wide=op=='concat' and int(re.search(r'word (\d+)',defs[oldid])[1])!=w
 if wide:
  s += [f' pose proof (@to_Zpos_ge0 (word_{n} (encoded_leaves s i ghost))) as lower.',f' pose proof (@to_Zpos_bounded (word_{n} (encoded_leaves s i ghost))) as upper.', f' rewrite encoded_word_{n}_size in upper.', f' rewrite concat_integer_{n} '+ ' '.join(known[k][0] for k in deps)+' in lower upper.']
 if op=='concat' and not wide:
  s += [f' transitivity (normalize {w} (to_Zpos (word_{n} (encoded_leaves s i ghost)))).',f' - symmetry. apply unsigned_normalized. apply encoded_word_{n}_size.',' -']
 s += [f' rewrite {op}_integer_{n} '+' '.join(known[k][0] for k in deps)+'.', ' unfold '+', '.join(f'Reference.v{k}' for k in unfold)+', Radix2Divider.CIRCTBits.word, normalize, modulus.']
 if op=='mux':s += [' repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;', ' rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;', ' repeat (rewrite Z.mod_mod; [|lia]); reflexivity.']
 elif wide:s += [' rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.', ' rewrite Z.shiftl_mul_pow2; last lia.', ' rewrite Z.add_comm. symmetry. apply Z.mod_small.', ' cbn [modulus Pos.of_succ_nat Z.of_nat Z.pow Z.pow_pos Pos.iter] in lower, upper |- *. lia.']
 else:s += [' rewrite Z.shiftl_mul_pow2; last lia.',f' apply (f_equal (fun z : Z => z mod (2 ^ Z.of_nat {w}))). apply Z.add_comm.']
 s += ['Qed.'];known[n]=(f'log2_{n}_reference',oldid);count+=1
s += ['Print Assumptions log2_207_reference.', 'Print Assumptions log2_367_reference.']
(H/'Log2.v').write_text('\n'.join(s)+'\n');print(count)
