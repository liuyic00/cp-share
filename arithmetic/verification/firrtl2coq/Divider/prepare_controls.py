#!/usr/bin/env python3
from pathlib import Path
import json,re
H=Path(__file__).resolve().parent;d=json.loads((H/'nodes.json').read_text());m=json.loads((H/'node-matches.json').read_text());leaf=set(d['inputs']+d['registers'])
raw=(H.parents[1]/'rocq/Generated/Radix2Divider.v').read_text();defs={int(k):v for k,v in re.findall(r'Definition v(\d+) .*? := (.*)\.',raw)}
known={}
for f in ['Slices','Reductions','Log2','ReferenceNodes','Muxes','LeafWords','ControlStart','Log2Bounds','ControlSpecial']:
 for name,n,o in re.findall(r'Lemma ((?:slice_|reduction_|log2_|node|mux_|leaf_|control_)(\d+)_reference) .*?= Reference.v(\d+) s i\.',(H/(f+'.v')).read_text(),re.S):known[int(n)]=(name,int(o))
known={k:v for k,v in known.items() if k not in leaf}
def operation(n):
 e=d['expressions'][str(n)]
 if e.startswith('(@Emux'):return f'mux_integer_{n}'
 if 'VarOrder.T Bcat ' in e:return f'concat_integer_{n}'
 if 'VarOrder.T Bdshl ' in e:return f'shift_{n}_integer'
 if e.startswith('(@Eprim_binop'):return f'scalar_integer_{n}'
 if e.startswith('(@Eprim_unop'):return f'slice_integer_{n}'
 if e.startswith('(@Eref'):return f'alias_{n}_shape'
 raise ValueError(e)
def refs(n):return sorted(set(map(int,re.findall(r'Eid VarOrder.T (\d+)',d['expressions'][str(n)]))))
s=[r'''From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From ArithmeticCommon Require Import BitvectorFacts NormalizationFacts.
From Divider Require Import Stable Representation Typing ReferenceNodes Slices Reductions Muxes MuxShapes Concats Log2 ScalarOps SliceOps LeafWords ControlStart Log2Bounds ControlSpecial ReferenceNormalization.
Local Open Scope Z_scope.
Lemma le_successor_lt z threshold : Z.leb (threshold + 1) z = Z.ltb threshold z.
Proof. destruct (Z.leb_spec0 (threshold + 1) z), (Z.ltb_spec0 threshold z); try reflexivity; lia. Qed.
Lemma normalized_eq_zero z : (if Z.eqb (normalize 1 z) 0 then 1 else 0) = Z.lxor (normalize 1 z) 1.
Proof.
 pose proof (normalize_range 1 z) as range. change (0 <= normalize 1 z < 2) in range.
 have cases : normalize 1 z = 0 \/ normalize 1 z = 1 by lia.
 destruct cases as [zero|one]; [rewrite zero|rewrite one]; reflexivity.
Qed.
Lemma known_bit_eq_zero z (fixed : normalize 1 z = z) : (if Z.eqb z 0 then 1 else 0) = Z.lxor z 1.
Proof. rewrite <- fixed. apply normalized_eq_zero. Qed.
Lemma normalize_zero width : normalize width 0 = 0.
Proof. apply Z.mod_0_l. pose proof (modulus_positive width). lia. Qed.
'''];count=0
for n in d['order']:
 if n in known or str(n) not in m or n in [413,414,415]:continue
 o=m[str(n)][0];w=d['widths'][str(n)];ow=int(re.search(r'word (\d+)',defs[o])[1]);stop=set()
 def endpoints(k,root=False):
  if k in leaf:return
  if k in known and not root:stop.add(known[k][1]);return
  for dep in refs(k):endpoints(dep)
 endpoints(n,True)
 def expandold(k,root=False):
  if k==399 and 13 in stop:return '(Reference.v13 s i)'
  if k in stop:return f'(Reference.v{k} s i)'
  return re.sub(r'\bv(\d+) s i',lambda z:expandold(int(z[1])),defs[k])
 rhs=expandold(o,True);rhs=re.sub(r'\bword\b','normalize',rhs);rhs=re.sub(r'\b((?:r\d+_|nio_|nctrl_|nreset)\w*)\b',r'Reference.\1',rhs)
 s += [f'Lemma control_{n}_reference s i ghost : to_Zpos (word_{n} (encoded_leaves s i ghost)) = Reference.v{o} s i.', 'Proof.',f' change (to_Zpos (word_{n} (encoded_leaves s i ghost)) = {rhs}).',f' transitivity (normalize {ow} (to_Zpos (word_{n} (encoded_leaves s i ghost)))).']
 if w==ow:s += [f' - symmetry. apply unsigned_normalized. apply encoded_word_{n}_size.']
 elif w<ow:s += [f' - symmetry. apply Z.mod_small. split; first apply to_Zpos_ge0.',f'   pose proof (@to_Zpos_bounded (word_{n} (encoded_leaves s i ghost))) as bound.',f'   rewrite encoded_word_{n}_size in bound. change (to_Zpos (word_{n} (encoded_leaves s i ghost)) < {2**w}) in bound.',f'   change (to_Zpos (word_{n} (encoded_leaves s i ghost)) < {2**ow}). lia.']
 else:raise ValueError((n,w,ow))
 s += [' -']
 rewrites=[];seen=set()
 def visit(k,root=False):
  if k in seen:return
  seen.add(k)
  if k in known and not root:rewrites.append(f'({known[k][0]} s i ghost)');return
  if k in leaf:rewrites.append(f'(leaf_{k}_integer s i ghost)');return
  rewrites.append(operation(k))
  for dep in refs(k):visit(dep)
 visit(n,True)
 for lemma in rewrites:s += [f' rewrite ?{lemma}.']
 literals=set()
 for node in seen:
  if node in leaf:continue
  for literal in re.findall(r'\[::[^]]*\]',d['expressions'][str(node)]):
   value=sum(2**j for j,b in enumerate(re.findall('true|false',literal)) if b=='true');literals.add((literal,value))
 for j,(literal,value) in enumerate(sorted(literals)):
  s += [f' have literal_{j} : to_Zpos {literal} = {value} by reflexivity.',f' rewrite ?literal_{j}.']
 for j,(width,value) in enumerate(sorted(set(re.findall(r'normalize (\d+) \((-?\d+)\)',rhs)))):
  s += [f' have constant_{j} : normalize {width} {value} = {int(value)%(2**int(width))} by reflexivity.',f' rewrite ?constant_{j}.']

 s += [' rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.']
 for oldendpoint in sorted(stop):
  s += [f' repeat (rewrite reference_{oldendpoint}_widen; [|lia]).']
  if int(re.search(r'word (\d+)',defs[oldendpoint])[1])==1:
   s += [f' rewrite ?(known_bit_eq_zero _ (reference_{oldendpoint}_normalized s i)).']
 s += [' rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.', ' rewrite ?(le_successor_lt _ 62).'  ,
 ' repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].',
 ' rewrite ?normalized_eq_zero.',
 ' repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];',
 ' repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];',
 f' rewrite ?reference_{o}_normalized; try reflexivity.', ' all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.',f' all: try (apply (f_equal (normalize {ow})); apply Z.land_comm).',' all: reflexivity.','Qed.']
 known[n]=(f'control_{n}_reference',o);count+=1
s+=['Print Assumptions control_482_reference.'];(H/'Controls.v').write_text('\n'.join(s)+'\n');print(count)
