#!/usr/bin/env python3
from pathlib import Path
import re,json
H=Path(__file__).resolve().parent;d=json.loads((H/'nodes.json').read_text());m=json.loads((H/'node-matches.json').read_text())
rep=(H/'Representation.v').read_text().split('Definition project_state')[0]
entries={int(k):(int(w),v) for k,w,v in re.findall(r'\| (\d+) => encode (\d+) (.*)',rep)}
s=['''From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths.
From ArithmeticCommon Require Import BitvectorFacts.
From Divider Require Import Stable Representation.
Local Open Scope Z_scope.
Lemma normalize_widen outer inner z (ordered : (inner <= outer)%coq_nat) : normalize outer (normalize inner z) = normalize inner z.
Proof.
 apply Z.mod_small. pose proof (normalize_range inner z) as bounds.
 assert (power : modulus inner <= modulus outer).
 { unfold modulus. apply Z.pow_le_mono_r; lia. }
 lia.
Qed.
''']
for n in sorted(d['inputs']+d['registers']):
 w,val=entries[n];val=val.replace('ghost_sign','ghost')
 s += [f'Transparent word_{n}.',f'Lemma leaf_{n}_integer s i ghost : to_Zpos (word_{n} (encoded_leaves s i ghost)) = normalize {w} {val}.',f'Proof. unfold word_{n}, encoded_leaves. apply decode_encode. Qed.',f'Opaque word_{n}.']
 if str(n) in m:
  o=m[str(n)][0]
  if n in [40,43,51]:
   inner,outer,zero,field={40:(64,65,26,'r5_nbReg'),43:(65,128,27,'r6_naValx2Reg'),51:(6,128,29,'r9_ncnt_5Fvalue')}[n]
   s += [f'Lemma leaf_{n}_reference s i ghost : to_Zpos (word_{n} (encoded_leaves s i ghost)) = Reference.v{o} s i.',f'Proof. rewrite leaf_{n}_integer. unfold Reference.v{o}, Reference.v{zero}, Radix2Divider.CIRCTBits.word.', f' change (normalize {inner} (Reference.{field} s) = normalize {outer} (normalize {inner} (Reference.{field} s))).', ' symmetry. apply normalize_widen. lia. Qed.']
   continue
  s += [f'Lemma leaf_{n}_reference s i ghost : to_Zpos (word_{n} (encoded_leaves s i ghost)) = Reference.v{o} s i.',f'Proof. rewrite leaf_{n}_integer. unfold Reference.v{o}, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.']
for n,dep in [(2,420),(8,419),(9,418)]:
 s += [f'Transparent word_{n}.',f'Lemma alias_{n}_shape v : word_{n} v = word_{dep} v.',f'Proof. unfold word_{n}, closed_{n}, expr_{n}, word_of_eval. reflexivity. Qed.',f'Opaque word_{n}.']
s+=['''Transparent word_376.
Lemma shift_376_shape v : word_376 v = zext_to 128 (zeros (to_nat (word_51 v)) ++ word_43 v).
Proof. unfold word_376, closed_376, expr_376, word_of_eval. reflexivity. Qed.
Opaque word_376.
Lemma shift_376_integer s i ghost : to_Zpos (word_376 (encoded_leaves s i ghost)) =
 Z.shiftl (to_Zpos (word_43 (encoded_leaves s i ghost))) (to_Zpos (word_51 (encoded_leaves s i ghost))).
Proof. rewrite shift_376_shape. unfold zext_to. rewrite unsigned_zero_extend unsigned_shift_left.
 rewrite -to_Zpos_nat. reflexivity. Qed.
Print Assumptions shift_376_integer.
''']
(H/'LeafWords.v').write_text('\n'.join(s)+'\n')
