from pathlib import Path
import json,re
H=Path(__file__).resolve().parent
g=json.loads((H/'global-dependencies.json').read_text());idx=json.loads((H/'global-key-index.json').read_text());instances=list(g['instances'].items())
header='''From Coq Require Import ZArith NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalWidthFacts GlobalChildBits GlobalAliases Compressors.
Local Open Scope Z_scope.
'''
s=header
for num,(p,mid) in enumerate(instances):
 if mid==3:continue
 args=['a','b','c','d','e'][:[2,3,5][mid]];outs=[[4,5],[5,6],[7,8,9]][mid];pred=[15,19,34][mid]
 inp=[idx[p+':'+str(j+2)] for j in range(len(args))];out=[idx[p+':'+str(j)] for j in outs]
 s+=f'Lemma instance_{num}_weight v (sizes:global_leaf_sizes v) :\n'
 s+=' + '.join(f'to_Zpos (global_word_{n} v)' for n in inp)+' = '+' + '.join(f'{1 if j==0 else 2} * to_Zpos (global_word_{n} v)' for j,n in enumerate(out))+'.\nProof.\n'
 for a,n in zip(args,inp):s+=f' destruct (one_bit_form _ (global_size_{n} v sizes)) as [{a} E{a}].\n'
 s+=f' destruct (instance_{num}_bits v {" ".join(args)} '+ ' '.join('E'+a for a in args)+') as ['+' [ '.join('Out'+str(j) for j in range(len(out)))+' Assert'+']'*len(out)+'.\n'
 s+=' rewrite '+' '.join(['E'+a for a in args]+['Out'+str(j) for j in range(len(out))])+'.\n'
 s+=' destruct '+','.join(args)+'; reflexivity.\nQed.\n'
 s+=f'Lemma instance_{num}_assert v (sizes:global_leaf_sizes v) : global_word_{idx[p+":"+str(pred)]} v=[::true].\nProof.\n'
 for a,n in zip(args,inp):s+=f' destruct (one_bit_form _ (global_size_{n} v sizes)) as [{a} E{a}].\n'
 s+=f' destruct (instance_{num}_bits v {" ".join(args)} '+ ' '.join('E'+a for a in args)+') as ['+' [ '.join('Out'+str(j) for j in range(len(out)))+' Assert'+']'*len(out)+'. exact Assert.\nQed.\n'
(H/'GlobalChildWeights.v').write_text(s)
s=header
widths=(H/'GlobalWidths.v').read_text()
for k,node in g['nodes'].items():
 n=idx[k]
 if node.get('expr','').startswith('(@Eprim_unop VarOrder.T (Uextr 0 0)') and len(node['deps'])==1:
  dn=idx[node['deps'][0]]
  if not re.search(rf'Lemma global_size_{dn} v .*?size \(global_word_{dn} v\)=1%nat\.',widths):continue
  s+=f'''Transparent global_word_{n}.
Lemma bit_wire_{n} v (sizes:global_leaf_sizes v) : global_word_{n} v=global_word_{dn} v.
Proof.
 destruct (one_bit_form _ (global_size_{dn} v sizes)) as [bit E].
 unfold global_word_{n}, global_closed_{n}, global_expr_{n}, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_{n}.
'''
s+='''Transparent global_word_362.
Lemma constant_wire_362 v : global_word_362 v=[::false].
Proof. reflexivity. Qed.
Opaque global_word_362.
'''
(H/'GlobalBitWires.v').write_text(s)
