from pathlib import Path
import json,re
H=Path(__file__).resolve().parent
g=json.loads((H/'global-dependencies.json').read_text());idx=json.loads((H/'global-key-index.json').read_text())
s='''From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import BitvectorFacts.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalAliases GlobalBitWires GlobalContracts Compression8 NodeFacts.
Local Open Scope Z_scope.
'''
seen=set();cats=[]
def visit(k):
 if k in seen:return
 node=g['nodes'][k]
 if ' Bcat ' not in node.get('expr',''):return
 seen.add(k)
 for d in node['deps']:visit(d)
 cats.append(k)
visit(':387');visit(':401')
widthtext=(H/'GlobalWidths.v').read_text()
for k in cats:
 n=idx[k];ns=list(map(int,re.findall(r'\(@Eid VarOrder.T (\d+)\)',g['nodes'][k]['expr'])))
 hi=idx[':'+str(ns[0])];lo=idx[':'+str(ns[1])] if len(ns)>1 else None
 loexpr=f'global_word_{lo} v' if lo is not None else '[::false;false]'
 lowidth=int(re.search(rf'Lemma global_size_{lo} v .*?size \(global_word_{lo} v\)=(\d+)%nat\.',widthtext)[1]) if lo is not None else 2
 s+=f'''Transparent global_word_{n}.
Lemma output_cat_{n} v : global_word_{n} v = ({loexpr}) ++ global_word_{hi} v.
Proof.
 unfold global_word_{n}, global_closed_{n}, global_expr_{n}, Stable.word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 reflexivity.
Qed.
Opaque global_word_{n}.
Lemma output_cat_integer_{n} v (sizes:global_leaf_sizes v) :
 to_Zpos (global_word_{n} v) = {('to_Zpos (global_word_'+str(lo)+' v)') if lo is not None else '0'} + to_Zpos (global_word_{hi} v) * {2**lowidth}.
Proof. rewrite output_cat_{n} unsigned_cat.'''
 s+=f' rewrite (global_size_{lo} v sizes).' if lo is not None else ''
 s+=' reflexivity. Qed.\n'
s+='''Lemma output_rows_match v (sizes:global_leaf_sizes v) :
 to_Zpos (global_word_1276 v) + to_Zpos (global_word_1290 v) = output_rows (global_compressor_outputs v).
Proof.
'''
s+=' rewrite '+' '.join(f'(output_cat_integer_{idx[k]} v sizes)' for k in reversed(cats))+'.\n'
# Follow output bit wires through aliases to the child output ports used by global_compressor_outputs.
stops=set()
for p,m in g['instances'].items():
 if p and '/' not in p:
  for o in [[4,5],[5,6],[7,8,9]][m]:stops.add(p+':'+str(o))
bitwires=set(map(int,re.findall(r'Lemma bit_wire_(\d+)',(H/'GlobalBitWires.v').read_text())))
front=set(d for k in cats for d in g['nodes'][k]['deps'] if d not in seen)
chain=[]
for k in front:
 while k not in stops:
  node=g['nodes'][k];n=idx[k]
  if node['kind'].startswith('sync') or node.get('expr','').startswith('(@Eref '):chain.append('wire_alias_'+str(n))
  elif n in bitwires:chain.append(f'(bit_wire_{n} v sizes)')
  else:raise Exception(k)
  k=node['deps'][0]
s+=' rewrite '+' '.join('?'+x for x in chain)+'.\n'
s+=' unfold output_rows. cbn [global_compressor_outputs nth]. ring.\nQed.\n'
s+='''Transparent global_word_1291 global_word_1292.
Lemma output_add_bits v : global_word_1291 v = from_N 17 (to_N (global_word_1276 v) + to_N (global_word_1290 v)).
Proof.
 unfold global_word_1291, global_closed_1291, global_expr_1291, Stable.word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
Qed.
Lemma output_truncate_bits v : global_word_1292 v = take 16 (global_word_1291 v).
Proof.
 unfold global_word_1292, global_closed_1292, global_expr_1292, Stable.word_of_eval.
 cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; [reflexivity|reflexivity].
Qed.
Opaque global_word_1291 global_word_1292.
Theorem global_output_weight v (sizes:global_leaf_sizes v) :
 to_Zpos (global_word_1299 v) = weighted_registers (global_register_numbers v) mod 65536.
Proof.
 rewrite wire_alias_1299 output_truncate_bits output_add_bits final_add_value.
 rewrite (output_rows_match v sizes). exact (global_compression_mod v sizes).
Qed.
'''
(H/'GlobalOutput.v').write_text(s)
