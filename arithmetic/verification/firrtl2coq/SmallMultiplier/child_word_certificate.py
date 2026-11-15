#!/usr/bin/env python3
from pathlib import Path
import re
H=Path(__file__).resolve().parent
out=['From Coq Require Import NArith ZArith.','From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.','From nbits Require Import NBits.','From SmallMultiplier Require Import Child0Stable Child1Stable Child2Stable Compressors.','Local Open Scope N_scope.']
for mid in range(3):
 s=(H/f'Child{mid}Stable.v').read_text();names=re.findall(r'Definition ((?:word|port)_\d+(?:_\d+)?) ',s)
 out+=['Transparent '+' '.join(f'Child{mid}Stable.{n}' for n in names)+'.']
out += ['''Definition c22_leaves (a b reset:bool) : Child0Stable.leaf_values :=
 fun scope id => [:: if scope == 0 then if id == 2 then a else if id == 3 then b else if id == 1 then reset else false else false].
Definition c32_leaves (a b c reset:bool) : Child1Stable.leaf_values :=
 fun scope id => [:: if scope == 0 then if id == 2 then a else if id == 3 then b else if id == 4 then c else if id == 1 then reset else false else false].
Definition c53_leaves (a b c d e reset:bool) : Child2Stable.leaf_values :=
 fun scope id => [:: if scope == 0 then if id == 2 then a else if id == 3 then b else if id == 4 then c else if id == 5 then d else if id == 6 then e else if id == 1 then reset else false
 else if scope == 10 then if id == 5 then fa_sum a b c else if id == 6 then fa_carry a b c else false
 else if scope == 11 then if id == 5 then fa_sum (fa_sum a b c) d e else if id == 6 then fa_carry (fa_sum a b c) d e else false else false].''']
for mid,args,ports,results,pred in [(0,'a b reset',[4,5],['xorb a b','andb a b'],15),(1,'a b c reset',[5,6],['fa_sum a b c','fa_carry a b c'],19),(2,'a b c d e reset',[7,8,9],['fa_sum (fa_sum a b c) d e','fa_carry a b c','fa_carry (fa_sum a b c) d e'],34)]:
 leaf=['c22','c32','c53'][mid]+'_leaves'
 for port,result in zip(ports,results):
  out+=[f'Lemma child{mid}_word{port}_bits {args} : Child{mid}Stable.word_{port} ({leaf} {args}) = [::{result}].',f'Proof. destruct '+','.join(args.split())+'; vm_compute;reflexivity. Qed.']
 out +=[f'Lemma child{mid}_assert_bits {args} : Child{mid}Stable.word_{pred} ({leaf} {args}) = [::true].',f'Proof. destruct '+','.join(args.split())+'; vm_compute;reflexivity. Qed.']
suffix=(H/'ChildWords.v').read_text().split('Definition bool_Z',1)
(H/'ChildWords.v').write_text('\n'.join(out)+'\n'+('Definition bool_Z'+suffix[1] if len(suffix)>1 else ''))
