from pathlib import Path
import re
H=Path(__file__).resolve().parent
s='''From Coq Require Import NArith ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From SmallMultiplier Require Import Child0Stable Child1Stable Child2Stable Child0Congruence Child1Congruence Child2Congruence ChildWords Compressors GlobalWidthFacts.
Local Open Scope N_scope.
'''
for mid in range(3):
 names=re.findall(r'Definition ((?:word|port)_\d+(?:_\d+)?) ',(H/f'Child{mid}Stable.v').read_text())
 s+='Local Opaque '+' '.join(f'Child{mid}Stable.{n}' for n in names)+'.\n'
for mid,args,outs,results,pred in [(0,'a b',[4,5],['xorb a b','andb a b'],15),(1,'a b c',[5,6],['fa_sum a b c','fa_carry a b c'],19),(2,'a b c d e',[7,8,9],['fa_sum (fa_sum a b c) d e','fa_carry a b c','fa_carry (fa_sum a b c) d e'],34)]:
 name=['c22','c32','c53'][mid]+'_leaves'
 params=[(0,i+2,a) for i,a in enumerate(args.split())]
 if mid==2:params +=[(10,6,'fa_carry a b c'),(11,5,'fa_sum (fa_sum a b c) d e'),(11,6,'fa_carry (fa_sum a b c) d e')]
 for out,expr in [*zip(outs,results),(pred,'true')]:
  deps=re.search(rf'Lemma word_{out}_inputs v w (.*?) : word_', (H/f'Child{mid}Congruence.v').read_text())[1]
  refs=[tuple(map(int,x)) for x in re.findall(r'v (\d+) (\d+)',deps)]
  selected=[p for p in params if p[:2] in refs]
  s+=f'Lemma abstract_child{mid}_{out} (v:Child{mid}Stable.leaf_values) ({args}:bool)\n'
  for scope,id,value in selected:s+=f' (E{scope}_{id}:v {scope} {id} = [::{value}])\n'
  s+=f' : Child{mid}Stable.word_{out} v = [::{expr}].\nProof.\n'
  s+=f' transitivity (Child{mid}Stable.word_{out} ({name} {args} false)).\n'
  s+=f' - apply Child{mid}Congruence.word_{out}_inputs.\n'
  for scope,id in refs:s+=f'   + exact E{scope}_{id}.\n'
  s+=f' - apply child{mid}_'+('assert_bits' if out==pred else f'word{out}_bits')+'.\nQed.\n'
(H/'ChildAbstract.v').write_text(s)
