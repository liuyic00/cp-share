#!/usr/bin/env python3
"""Generate checked slice composition and integer-reference certificates."""
from pathlib import Path
import json,re,sys
H=Path(__file__).resolve().parent
d=json.loads((H/'nodes.json').read_text());matches=json.loads((H/'node-matches.json').read_text())
widths={int(k):v for k,v in d['widths'].items()};leaf=set(d['registers']+d['inputs']);slices={}
lines=['''From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths
 HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths.
From ArithmeticCommon Require Import BitvectorFacts.
From Divider Require Import Stable Representation.
Local Open Scope N_scope.
Lemma slice_drop_take count start (xs : bits) :
 drop start (take count xs) = take (count - start) (drop start xs).
Proof.
 revert count start. induction xs as [|b xs IH]; intros [|count] [|start]; cbn; try reflexivity.
 - by rewrite take0.
 - apply IH.
Qed.
Lemma slice_take_take first second (xs : bits) :
 take first (take second xs) = take (minn first second) xs.
Proof.
 revert first second. induction xs as [|b xs IH]; intros [|first] [|second]; cbn; try reflexivity.
 rewrite minnSS. cbn. rewrite IH. reflexivity.
Qed.
''']
for id in d['order']:
 e=d['expressions'][str(id)]
 m=re.fullmatch(r'\(@Eprim_unop VarOrder.T \(Uextr (\d+) (\d+)\) \(@Eref VarOrder.T \(@Eid VarOrder.T (\d+)\)\)\)',e)
 if not m:continue
 hi,lo,dep=map(int,m.groups());w=hi+1-lo
 if dep in leaf:root=dep;offset=lo
 elif dep in slices:root,offset,_=slices[dep];offset+=lo
 else:continue
 slices[id]=(root,offset,w)
 lines += [f'Transparent word_{id}.',f'Lemma slice_{id} v : word_{id} v = take {w} (drop {offset} (v {root})).',
 'Proof.',f' unfold word_{id}, closed_{id}, expr_{id}, word_of_eval.',
 f' change (drop {lo} (take {hi+1} (word_{dep} v)) = take {w} (drop {offset} (v {root}))).']
 if dep in leaf:lines += [f' Transparent word_{dep}.',f' unfold word_{dep}.']
 else:lines += [f' rewrite slice_{dep}.']
 lines += [' rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.','Qed.',f'Opaque word_{id}.']
 if dep in leaf:lines += [f'Opaque word_{dep}.']
 if str(id) in matches and '--composition-only' not in sys.argv:
  old=matches[str(id)][0]
  lines += [f'Lemma slice_{id}_reference s i ghost : to_Zpos (word_{id} (encoded_leaves s i ghost)) = Reference.v{old} s i.',
  f'Proof. rewrite slice_{id} unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.',
  f' unfold Reference.v{old}, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.']
lines += ['Print Assumptions slice_53.']
(H/'Slices.v').write_text('\n'.join(lines)+'\n');print('Slice certificates:',len(slices))
