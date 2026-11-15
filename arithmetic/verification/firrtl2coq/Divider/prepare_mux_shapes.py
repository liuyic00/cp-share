#!/usr/bin/env python3
from pathlib import Path
import json,re
H=Path(__file__).resolve().parent;d=json.loads((H/'nodes.json').read_text())
ref=r'\(@Eref VarOrder.T \(@Eid VarOrder.T \d+\)\)'
const=r'\(@Econst VarOrder.T \(Fuint \d+\) \[::[^]]*\]\)'
branch=f'(?:{ref}|{const})'
pattern=re.compile(r'\(@Emux VarOrder.T ('+ref+') ('+branch+') ('+branch+r')\)')
def bits(e,v):
 if e.startswith('(@Eref'):return 'word_'+re.search(r'Eid VarOrder.T (\d+)',e)[1]+' '+v
 return re.search(r'(\[::[^]]*\])',e)[1]
s=['''From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths.
From ArithmeticCommon Require Import BitvectorFacts.
From Divider Require Import Stable Representation Typing Muxes.
Local Open Scope Z_scope.
Lemma unsigned_adapt width bits : to_Zpos (zext_to width (take width bits)) = normalize width (to_Zpos bits).
Proof. unfold zext_to. rewrite unsigned_zero_extend unsigned_take. reflexivity. Qed.
'''];count=0
for n in d['order']:
 q=pattern.fullmatch(d['expressions'][str(n)])
 if not q:continue
 g=int(re.search(r'Eid VarOrder.T (\d+)',q[1])[1]);w=d['widths'][str(n)]
 a,b=bits(q[2],'v'),bits(q[3],'v');ae,be=bits(q[2],'(encoded_leaves s i ghost)'),bits(q[3],'(encoded_leaves s i ghost)');count+=1
 s += [f'Transparent word_{n}.',f'Lemma mux_shape_{n} v : word_{n} v = if is_zero (word_{g} v) then zext_to {w} (take {w} ({b})) else zext_to {w} (take {w} ({a})).',
 f'Proof. unfold word_{n}, closed_{n}, expr_{n}, word_of_eval.',
 ''' cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].''',
 f''' destruct (is_zero (word_{g} v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.''',f'Opaque word_{n}.',
 f'Lemma mux_integer_{n} s i ghost : to_Zpos (word_{n} (encoded_leaves s i ghost)) = normalize {w} (if Z.eqb (to_Zpos (word_{g} (encoded_leaves s i ghost))) 1 then to_Zpos ({ae}) else to_Zpos ({be})).',
 f'Proof. rewrite mux_shape_{n} (is_zero_onebit _ (encoded_word_{g}_size s i ghost)).',f' destruct (Z.eqb (to_Zpos (word_{g} (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.']
s+=['Print Assumptions mux_integer_418.'];(H/'MuxShapes.v').write_text('\n'.join(s)+'\n');print(count)
