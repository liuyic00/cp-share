#!/usr/bin/env python3
from pathlib import Path
import json,re
H=Path(__file__).resolve().parent
d=json.loads((H/'nodes.json').read_text());m=json.loads((H/'node-matches.json').read_text())
slices=set(map(int,re.findall(r'Lemma slice_(\d+)_reference',(H/'Slices.v').read_text())))
s=['''From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths.
From ArithmeticCommon Require Import BitvectorFacts.
From Divider Require Import Stable Representation ReferenceNodes Slices Typing.
Local Open Scope Z_scope.
Lemma fold_or_nonzero bits : foldr orb false bits = negb (is_zero bits).
Proof. induction bits as [|bit bits IH]; first reflexivity.
 destruct bit; cbn [foldr is_zero all]; [reflexivity|exact IH]. Qed.
'''];count=0
for n in d['order']:
 q=re.fullmatch(r'\(@Eprim_unop VarOrder.T Uorr \(@Eref VarOrder.T \(@Eid VarOrder.T (\d+)\)\)\)',d['expressions'][str(n)])
 if not q or str(n) not in m:continue
 dep=int(q[1])
 if dep not in slices:continue
 old=m[str(n)][0];olddep=m[str(dep)][0];count+=1
 if d['widths'][str(dep)]==1:
  s += [f'Transparent word_{n}.',f'Lemma reduction_{n}_reference s i ghost : to_Zpos (word_{n} (encoded_leaves s i ghost)) = Reference.v{old} s i.',
  f'Proof. unfold word_{n}, closed_{n}, expr_{n}, word_of_eval.',
  f' change (to_Zpos [::foldr orb false (word_{dep} (encoded_leaves s i ghost))] = Reference.v{old} s i).',
  f' rewrite -(slice_{dep}_reference s i ghost).',
  f' pose proof (encoded_word_{dep}_size s i ghost) as sized.',
  f' destruct (word_{dep} (encoded_leaves s i ghost)) as [|bit bits]; first discriminate.',
  ' destruct bits; last discriminate. destruct bit; reflexivity. Qed.',f'Opaque word_{n}.']
  continue

 s += [f'Transparent word_{n}.',f'Lemma reduction_{n}_reference s i ghost : to_Zpos (word_{n} (encoded_leaves s i ghost)) = Reference.v{old} s i.',
 f'Proof. unfold word_{n}, closed_{n}, expr_{n}, word_of_eval.',
 f' change (to_Zpos [::foldr orb false (word_{dep} (encoded_leaves s i ghost))] = Reference.v{old} s i).',
 f' rewrite unsigned_singleton fold_or_nonzero is_zero_unsigned slice_{dep}_reference.',
 f' unfold Reference.v{old}, Radix2Divider.CIRCTBits.word.',
 f' change ((if negb (Z.eqb (Reference.v{olddep} s i) 0) then 1 else 0) = ((if negb (Z.eqb (Reference.v{olddep} s i) 0) then 1 else 0) mod 2)).',
 f' destruct (Z.eqb (Reference.v{olddep} s i) 0); reflexivity. Qed.',f'Opaque word_{n}.']
s+=['Print Assumptions reduction_55_reference.'];(H/'Reductions.v').write_text('\n'.join(s)+'\n');print('reductions',count)
