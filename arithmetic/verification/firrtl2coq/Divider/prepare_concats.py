#!/usr/bin/env python3
from pathlib import Path
import json,re
H=Path(__file__).resolve().parent;d=json.loads((H/'nodes.json').read_text())
ref=r'\(@Eref VarOrder.T \(@Eid VarOrder.T \d+\)\)';const=r'\(@Econst VarOrder.T \(Fuint \d+\) \[::[^]]*\]\)';branch=f'(?:{ref}|{const})'
pattern=re.compile(r'\(@Eprim_binop VarOrder.T Bcat ('+branch+') ('+branch+r')\)')
def bits(e,v):
 if e.startswith('(@Eref'):return 'word_'+re.search(r'Eid VarOrder.T (\d+)',e)[1]+' '+v
 return re.search(r'(\[::[^]]*\])',e)[1]
s=['''From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths.
From ArithmeticCommon Require Import BitvectorFacts.
From Divider Require Import Stable Representation Typing.
Local Open Scope Z_scope.
'''];count=0
for n in d['order']:
 q=pattern.fullmatch(d['expressions'][str(n)])
 if not q:continue
 a,b=bits(q[1],'v'),bits(q[2],'v');ae,be=bits(q[1],'(encoded_leaves s i ghost)'),bits(q[2],'(encoded_leaves s i ghost)');count+=1
 dep=re.search(r'Eid VarOrder.T (\d+)',q[2]);bw=d['widths'][dep[1]] if dep else int(re.search(r'Fuint (\d+)',q[2])[1])
 s += [f'Transparent word_{n}.',f'Lemma concat_shape_{n} v : word_{n} v = ({b}) ++ ({a}).',
 f'''Proof. unfold word_{n}, closed_{n}, expr_{n}, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.''',f'Opaque word_{n}.',
 f'Lemma concat_integer_{n} s i ghost : to_Zpos (word_{n} (encoded_leaves s i ghost)) = to_Zpos ({be}) + to_Zpos ({ae}) * modulus {bw}.',f'Proof. rewrite concat_shape_{n} unsigned_cat.']
 if dep:s += [f' rewrite encoded_word_{dep[1]}_size.']
 s += [' reflexivity. Qed.']
s+=['Print Assumptions concat_integer_76.'];(H/'Concats.v').write_text('\n'.join(s)+'\n');print(count)
