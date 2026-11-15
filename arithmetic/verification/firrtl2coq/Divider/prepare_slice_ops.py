#!/usr/bin/env python3
from pathlib import Path
import json,re
H=Path(__file__).resolve().parent;d=json.loads((H/'nodes.json').read_text())
s=['''From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths.
From ArithmeticCommon Require Import BitvectorFacts.
From Divider Require Import Stable Representation Slices.
Local Open Scope Z_scope.
Lemma unsigned_slice width offset bits : to_Zpos (take width (drop offset bits)) = normalize width (Z.shiftr (to_Zpos bits) (Z.of_nat offset)).
Proof. rewrite unsigned_take unsigned_drop. reflexivity. Qed.
'''];count=0
for n in d['order']:
 e=d['expressions'][str(n)]
 q=re.fullmatch(r'\(@Eprim_unop VarOrder.T \(Uextr (\d+) (\d+)\) \(@Eref VarOrder.T \(@Eid VarOrder.T (\d+)\)\)\)',e)
 t=re.fullmatch(r'\(@Eprim_unop VarOrder.T \(Utail (\d+)\) \(@Eref VarOrder.T \(@Eid VarOrder.T (\d+)\)\)\)',e)
 if not q and not t:continue
 w=d['widths'][str(n)];lo=int(q[2]) if q else 0;dep=int(q[3]) if q else int(t[2]);count+=1
 s += [f'Transparent word_{n}.',f'Lemma slice_shape_{n} v : word_{n} v = take {w} (drop {lo} (word_{dep} v)).',f'Proof. unfold word_{n}, closed_{n}, expr_{n}, word_of_eval.']
 if q:s += [f' change (drop {lo} (take {int(q[1])+1} (word_{dep} v)) = take {w} (drop {lo} (word_{dep} v))).',' rewrite slice_drop_take. reflexivity. Qed.']
 else:s += [' rewrite drop0. reflexivity. Qed.']
 s += [f'Opaque word_{n}.',f'Lemma slice_integer_{n} s i ghost : to_Zpos (word_{n} (encoded_leaves s i ghost)) = normalize {w} (Z.shiftr (to_Zpos (word_{dep} (encoded_leaves s i ghost))) {lo}).',f'Proof. rewrite slice_shape_{n}. apply unsigned_slice. Qed.']
s+=['Print Assumptions slice_integer_481.'];(H/'SliceOps.v').write_text('\n'.join(s)+'\n');print(count)
