from pathlib import Path
import json,re
H=Path(__file__).resolve().parent
g=json.loads((H/'global-dependencies.json').read_text());idx=json.loads((H/'global-key-index.json').read_text());instances=list(g['instances'].items());nums={p:n for n,(p,_) in enumerate(instances)}
tops=[(p,m) for p,m in instances if p and '/' not in p];regs=list(range(201,305,2));stops={':'+str(n) for n in regs}
for p,m in tops:
 for o in [[4,5],[5,6],[7,8,9]][m]:stops.add(p+':'+str(o))
bitwires=set(map(int,re.findall(r'Lemma bit_wire_(\d+)',(H/'GlobalBitWires.v').read_text())))
def chain(k):
 out=[]
 while k not in stops:
  n=idx[k];node=g['nodes'][k]
  if node['kind'].startswith('sync') or node.get('expr','').startswith('(@Eref '):out.append(f'wire_alias_{n}')
  elif n in bitwires:out.append(f'(bit_wire_{n} v sizes)')
  elif n==362:out.append('constant_wire_362');break
  else:raise Exception(k)
  k=node['deps'][0]
 return out
s='''From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From SmallMultiplier Require Import GlobalStable GlobalWidths GlobalAliases GlobalBitWires GlobalChildWeights Compression8.
Local Open Scope Z_scope.
Definition global_register_numbers (v:global_leaves) (index:nat) : Z := nth 0 [::
'''
s+=';\n'.join(f'to_Zpos (global_word_{idx[":"+str(n)]} v)' for n in regs)+'] index.\n'
s+='Definition global_compressor_outputs (v:global_leaves) (index bit:nat) : Z := nth 0 (nth [::] [::\n'
s+=';\n'.join('[::'+';'.join(f'to_Zpos (global_word_{idx[p+":"+str(o)]} v)' for o in [[4,5],[5,6],[7,8,9]][m])+']' for p,m in tops)+'] index) bit.\n'
s+='''Lemma global_compressor_contracts v (sizes:global_leaf_sizes v) : compressor_contracts (global_register_numbers v) (global_compressor_outputs v).
Proof.
 unfold compressor_contracts. repeat split.
'''
for p,m in tops:
 ch=[]
 for id in range(2,[4,5,7][m]):ch+=chain(p+':'+str(id))
 # Preserve traversal order: after unfolding a later chain a shared alias may recur, hence ? repeats.
 s+=f' - have H := instance_{nums[p]}_weight v sizes.\n'
 s+='   rewrite '+' '.join('?'+x for x in ch)+' in H.\n'
 s+='   try change (to_Zpos [::false]) with 0 in H.\n'
 s+='   cbn [global_register_numbers global_compressor_outputs nth]. lia.\n'
s+='Qed.\n'
s+='''Lemma global_compression_mod v (sizes:global_leaf_sizes v) :
 output_rows (global_compressor_outputs v) mod 65536 = weighted_registers (global_register_numbers v) mod 65536.
Proof. apply compression_mod. apply global_compressor_contracts. exact sizes. Qed.
'''
(H/'GlobalContracts.v').write_text(s)
