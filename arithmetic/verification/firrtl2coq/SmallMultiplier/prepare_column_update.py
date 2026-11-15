from pathlib import Path
import re,json
H=Path(__file__).resolve().parent
entries=[tuple(map(int,x)) for x in re.findall(r'Build_capture_entry (\d+) (\d+) (\d+) (\d+) (\d+)',(H/'CaptureAST.v').read_text())]
idx=json.loads((H/'global-key-index.json').read_text())
s=r'''From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From SmallMultiplier Require Import GlobalStable GlobalWidths GlobalTop GlobalContracts Compression8 Packing8 CaptureNumbers PipelineCommit PipelineEquations RuntimeWords Booth8.
Local Open Scope Z_scope.
Theorem next_columns_weight v (sizes:global_leaf_sizes v) :
 weighted_registers(global_register_numbers(next_register_leaves v)) =
 if is_zero(global_word_56 v) then weighted_registers(global_register_numbers v)
 else weighted_registers(captured_register_numbers v).
Proof.
 unfold weighted_registers,global_register_numbers,captured_register_numbers. cbn [nth].
'''
s=s.replace('Theorem next_columns_weight', 'Local Opaque '+' '.join('global_word_'+str(n) for n in range(2262))+' '+' '.join('next_word_'+str(r) for r,m,b,p,k in entries)+'.\n'+'Theorem next_columns_weight')
# Expose only leaf access on the next-register function; never unfold a circuit DAG.

s+='Local Transparent '+' '.join(f'global_word_{idx[":"+str(r)]}' for r,m,b,p,k in entries)+'.\n'
s+=' cbn ['+' '.join(f'global_word_{idx[":"+str(r)]}' for r,m,b,p,k in entries)+' next_register_leaves N.of_nat Pos.of_succ_nat].\n'
s+=' rewrite '+' '.join(f'(capture_next_{r} v sizes)' for r,m,b,p,k in entries)+'.\n destruct (is_zero(global_word_56 v)); reflexivity.\nQed.\n'
s+=r'''Theorem captured_columns_product v a b
 (sizes:global_leaf_sizes v)
 (Ha:global_word_2 v=from_N 8 a) (Hb:global_word_53 v=from_N 8 b)
 (Hamin:N.lt a 256) (Hbmin:N.lt b 256) :
 weighted_registers(captured_register_numbers v) mod 65536 =
 (signed8(Z.of_N a)*signed8(Z.of_N b)) mod 65536.
Proof.
 rewrite (captured_weight_rows v sizes).
 replace (1 * to_Zpos(global_word_96 v)+1 * to_Zpos(global_word_132 v)+4*to_Zpos(global_word_169 v)+16*to_Zpos(global_word_205 v)+64*to_Zpos(global_word_223 v)) with
 (to_Zpos(global_word_96 v)+to_Zpos(global_word_132 v)+4*to_Zpos(global_word_169 v)+16*to_Zpos(global_word_205 v)+64*to_Zpos(global_word_223 v)) by ring.
 exact(global_packed_product v a b Ha Hb Hamin Hbmin).
Qed.
Theorem next_columns_product v a b
 (sizes:global_leaf_sizes v)
 (Ha:global_word_2 v=from_N 8 a) (Hb:global_word_53 v=from_N 8 b)
 (Hamin:N.lt a 256) (Hbmin:N.lt b 256)
 (enabled:is_zero(global_word_56 v)=false) :
 weighted_registers(global_register_numbers(next_register_leaves v)) mod 65536 =
 (signed8(Z.of_N a)*signed8(Z.of_N b)) mod 65536.
Proof. rewrite (next_columns_weight v sizes) enabled. exact(captured_columns_product v a b sizes Ha Hb Hamin Hbmin). Qed.
'''
(H/'ColumnUpdate.v').write_text(s)
