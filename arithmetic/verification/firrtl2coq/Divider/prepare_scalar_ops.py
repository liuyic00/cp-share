#!/usr/bin/env python3
from pathlib import Path
import json,re
H=Path(__file__).resolve().parent;d=json.loads((H/'nodes.json').read_text())
ref=r'\(@Eref VarOrder.T \(@Eid VarOrder.T \d+\)\)';const=r'\(@Econst VarOrder.T \(Fuint \d+\) \[::[^]]*\]\)';branch=f'(?:{ref}|{const})'
pattern=re.compile(r'\(@Eprim_binop VarOrder.T (\(Bcomp \w+\)|Badd|Bsub|Bmul|Band|Bxor) ('+branch+') ('+branch+r')\)')
def bits(e,v):
 if e.startswith('(@Eref'):return 'word_'+re.search(r'Eid VarOrder.T (\d+)',e)[1]+' '+v
 return re.search(r'(\[::[^]]*\])',e)[1]
s=['''From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths.
From ArithmeticCommon Require Import BitvectorFacts.
From Divider Require Import Stable Representation Typing ReferenceNodes.
Local Open Scope Z_scope.
Lemma binary_lt_unsigned a b : N.ltb (to_N a) (to_N b) = Z.ltb (to_Zpos a) (to_Zpos b).
Proof.
 rewrite !to_Zpos_N. destruct (N.ltb_spec0 (to_N a) (to_N b)) as [lt|ge].
 - symmetry. apply Z.ltb_lt. apply N2Z.inj_lt. exact lt.
 - symmetry. apply Z.ltb_ge. apply N2Z.inj_le. apply N.nlt_ge. exact ge.
Qed.
Lemma binary_le_unsigned a b : N.leb (to_N a) (to_N b) = Z.leb (to_Zpos a) (to_Zpos b).
Proof.
 rewrite !to_Zpos_N. destruct (N.leb_spec0 (to_N a) (to_N b)) as [le|gt].
 - symmetry. apply Z.leb_le. apply N2Z.inj_le. exact le.
 - symmetry. apply Z.leb_gt. apply N2Z.inj_lt. apply N.nle_gt. exact gt.
Qed.
'''];count=0
for n in d['order']:
 q=pattern.fullmatch(d['expressions'][str(n)])
 if not q:continue
 op=q[1];a,b=bits(q[2],'v'),bits(q[3],'v');ae,be=bits(q[2],'(encoded_leaves s i ghost)'),bits(q[3],'(encoded_leaves s i ghost)');w=d['widths'][str(n)];count+=1
 if op=='Badd':shape=f'from_N {w} ((to_N ({a}) + to_N ({b}))%num)';integer=f'normalize {w} (to_Zpos ({ae}) + to_Zpos ({be}))';proof='apply unsigned_from_N_add.'
 elif op=='Bsub':shape=f'from_Z {w} (to_Zpos ({a}) - to_Zpos ({b}))';integer=f'normalize {w} (to_Zpos ({ae}) - to_Zpos ({be}))';proof='apply unsigned_from_Z.'
 elif op=='Bmul':shape=f'from_N {w} ((to_N ({a}) * to_N ({b}))%num)';integer=f'normalize {w} (to_Zpos ({ae}) * to_Zpos ({be}))';proof='apply unsigned_from_N_mul.'
 elif op in ['Band','Bxor']:
  shape=f'{"andB" if op=="Band" else "xorB"} ({a}) ({b})';integer=f'{"Z.land" if op=="Band" else "Z.lxor"} (to_Zpos ({ae})) (to_Zpos ({be}))';proof=f'apply unsigned_{"and" if op=="Band" else "xor"}.'
  for expr in [q[2],q[3]]:
   dep=re.search(r'Eid VarOrder.T (\d+)',expr)
   if dep:proof+=f' rewrite encoded_word_{dep[1]}_size.'
  proof+=' reflexivity.'
 else:
  kind=op[7:-1]
  if kind=='Beq':pred=f'to_N ({a}) == to_N ({b})';zp=f'Z.eqb (to_Zpos ({ae})) (to_Zpos ({be}))';rw='numeric_equality_unsigned'
  elif kind=='Bneq':pred=f'to_N ({a}) != to_N ({b})';zp=f'negb (Z.eqb (to_Zpos ({ae})) (to_Zpos ({be})))';rw='numeric_equality_unsigned'
  elif kind=='Blt':pred=f'N.ltb (to_N ({a})) (to_N ({b}))';zp=f'Z.ltb (to_Zpos ({ae})) (to_Zpos ({be}))';rw='binary_lt_unsigned'
  elif kind=='Bgeq':pred=f'N.leb (to_N ({b})) (to_N ({a}))';zp=f'Z.leb (to_Zpos ({be})) (to_Zpos ({ae}))';rw='binary_le_unsigned'
  else:raise ValueError(kind)
  shape=f'[:: {pred}]';integer=f'if {zp} then 1 else 0';proof=f'rewrite unsigned_singleton {rw}. reflexivity.'
 s += [f'Transparent word_{n}.',f'Lemma scalar_shape_{n} v : word_{n} v = {shape}.',
 f'''Proof. unfold word_{n}, closed_{n}, expr_{n}, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.''',f'Opaque word_{n}.',
 f'Lemma scalar_integer_{n} s i ghost : to_Zpos (word_{n} (encoded_leaves s i ghost)) = {integer}.',f'Proof. rewrite scalar_shape_{n}. {proof} Qed.']
s+=['Print Assumptions scalar_integer_483.'];(H/'ScalarOps.v').write_text('\n'.join(s)+'\n');print(count)
