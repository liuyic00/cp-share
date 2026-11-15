#!/usr/bin/env python3
"""Build the integer conservation certificate for the exact 8-bit FIRRTL wiring.
The generated theorem is a mathematical wiring lemma; interpreter bridge remains separate.
"""
from pathlib import Path
import re, argparse, collections
p=argparse.ArgumentParser();p.add_argument('firrtl',type=Path);a=p.parse_args()
s=a.firrtl.read_text().split('  module ArrayMulDataModule8 :')[1]
nodes=dict(re.findall(r'^    node (\w+) = (.+?)(?: @\[.*)?$',s,re.M))
instances=re.findall(r'^    inst (\w+) of (C22|C32|C53)',s,re.M)
conns=dict(re.findall(r'^    ([\w.]+) <= (.+?)(?: @\[.*)?$',s,re.M))
regid=lambda n:0 if n=='r' else int(n[2:])
weights={}
for r in ['r']+['r_'+str(i) for i in range(1,52)]:
 src=re.fullmatch(r'mux\(io_regEnables_0, (\w+), '+r+r'\)',nodes[conns[r]]).group(1)
 pp,k,k2=re.fullmatch(r'bits\((pp(?:_\d)?|finalCorrection), (\d+), (\d+)\)',nodes[src]).groups()
 assert k==k2
 weights[r]=2**(int(k)+{'pp':0,'pp_1':0,'pp_2':2,'pp_3':4,'finalCorrection':6}[pp])
atom={r:f'r {regid(r)}%nat' for r in weights}
cell_inputs=[]; cell_weights=[]
for idx,(name,typ) in enumerate(instances):
 count={'C22':2,'C32':3,'C53':5}[typ];outs={'C22':2,'C32':2,'C53':3}[typ]
 ins=[]; w=[]
 for j in range(count):
  ref=conns[f'{name}.io_in_{j}']
  if ref=='UInt<1>("h0")':ins.append('0');continue
  ins.append(atom[ref]);w.append(weights[ref])
 assert len(set(w))==1,(name,w)
 cell_inputs.append(ins);cell_weights.append(w[0])
 for j in range(outs):
  ref=f'{name}.io_out_{j}';atom[ref]=f'o {idx}%nat {j}%nat';weights[ref]=w[0]*(1 if j==0 else 2)
  for nod,expr in nodes.items():
   if expr==f'bits({ref}, 0, 0)':atom[nod]=atom[ref];weights[nod]=weights[ref]

def cat_atoms(ref):
 if ref in atom:return [ref]
 expr=nodes.get(ref,ref)
 m=re.fullmatch(r'cat\((\w+), (\w+)\)',expr)
 if m:return cat_atoms(m[2])+cat_atoms(m[1])
 m=re.fullmatch(r'cat\((\w+), UInt<(\d+)>\("h0"\)\)',expr)
 if m:return [None]*int(m[2])+cat_atoms(m[1])
 raise ValueError((ref,expr))
resultrefs=cat_atoms('sum')+[]
rowrefs=[cat_atoms('sum'),cat_atoms('carry_1')]
used=collections.Counter()
for refs in rowrefs:
 for bit,ref in enumerate(refs):
  if ref:
   assert weights[ref]==2**bit,(ref,weights[ref],bit)
   used[atom[ref]]+=2**bit
# Sum all weighted local conservation equations and cancel internal wires.
coeff=collections.Counter({atom[r]:w for r,w in weights.items() if re.fullmatch(r'r(?:_\d+)?',r)})
for i,((name,typ),ins,w) in enumerate(zip(instances,cell_inputs,cell_weights)):
 for x in ins:
  if x!='0':coeff[x]-=w
 for j in range(3 if typ=='C53' else 2):coeff[f'o {i}%nat {j}%nat']+=w*(1 if j==0 else 2)
remaining={x:v-used[x] for x,v in coeff.items() if v-used[x]}
assert all(v%65536==0 for v in remaining.values()),remaining
assert len(instances)==30
fmt=lambda terms:' + '.join(f'{w}*({x})' for x,w in terms if w) or '0'
regsum=fmt([(atom[r],weights[r]) for r in ['r']+['r_'+str(i) for i in range(1,52)]])
result=fmt(used.items());overflow=fmt([(x,v//65536) for x,v in remaining.items()])
contracts=[]
for i,((name,typ),ins) in enumerate(zip(instances,cell_inputs)):
 outs=fmt([(f'o {i}%nat {j}%nat',1 if j==0 else 2) for j in range(3 if typ=='C53' else 2)])
 contracts.append('('+' + '.join(f'({x})' for x in ins)+' = '+outs+')')
out='''From Coq Require Import ZArith Lia.\nOpen Scope Z_scope.\n(* Exact scalar wiring of ArrayMulDataModule8, generated from the retained Low FIRRTL.\n   The interpreter-to-contract bridge is a separate obligation. *)\n'''
out+='Definition compressor_contracts (r : nat -> Z) (o : nat -> nat -> Z) : Prop :=\n  '+' /\\\n  '.join(contracts)+'.\n'
out+=f'Definition weighted_registers (r : nat -> Z) := {regsum}.\n'
out+=f'Definition output_rows (o : nat -> nat -> Z) := {result}.\n'
out+=f'Definition overflow_carries (o : nat -> nat -> Z) := {overflow}.\n'
out+='''Theorem compression_conserves r o (H : compressor_contracts r o) :
 weighted_registers r = output_rows o + 65536 * overflow_carries o.
Proof.
 unfold compressor_contracts in H. repeat match type of H with _ /\\ _ => destruct H as [? H] end.
 unfold weighted_registers,output_rows,overflow_carries. lia.
Qed.
Theorem compression_mod r o (H : compressor_contracts r o) :
 output_rows o mod 65536 = weighted_registers r mod 65536.
Proof.
 rewrite (compression_conserves r o H).
 rewrite Z.add_mod, Z.mul_mod by lia.
 rewrite Z.mod_same, Z.mul_0_l, Z.mod_0_l, Z.add_0_r, Z.mod_mod by lia. reflexivity.
Qed.
Print Assumptions compression_mod.
'''
Path(__file__).with_name('Compression8.v').write_text(out)
print('30 cell equations; discarded terms:',remaining)
