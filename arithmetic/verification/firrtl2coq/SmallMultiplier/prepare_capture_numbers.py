from pathlib import Path
import json,re
H=Path(__file__).resolve().parent
idx=json.loads((H/'global-key-index.json').read_text())
entries=[tuple(map(int,x)) for x in re.findall(r'Build_capture_entry (\d+) (\d+) (\d+) (\d+) (\d+)',(H/'CaptureAST.v').read_text())]
s=r'''From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import BitvectorFacts NormalizationFacts.
From SmallMultiplier Require Import Stable GlobalStable GlobalWidths Packing8 Compression8.
Local Open Scope Z_scope.
'''
s+='Local Opaque '+' '.join('global_word_'+str(n) for n in range(2262))+'.\n'
for r,m,b,p,k in entries:
 bi,pi=[idx[':'+str(x)] for x in (b,p)]
 s+=f'''Local Transparent global_word_{bi}.
Lemma capture_bit_{b} v : global_word_{bi} v = drop {k} (take {k+1} (global_word_{pi} v)).
Proof.
 unfold global_word_{bi},global_closed_{bi},global_expr_{bi},word_of_eval.
 cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; [|reflexivity]. reflexivity.
Qed.
Local Opaque global_word_{bi}.
Lemma capture_integer_{b} v (sizes:global_leaf_sizes v) : to_Zpos(global_word_{bi} v)=extract_bit (to_Zpos(global_word_{pi} v)) {k}%nat.
Proof.
 rewrite -(unsigned_normalized 1 (global_word_{bi} v) (global_size_{bi} v sizes)).
 rewrite capture_bit_{b} unsigned_drop unsigned_take normalize_shiftr_nested; [|lia].
 unfold normalize,modulus,extract_bit. rewrite Z.shiftr_div_pow2; [reflexivity|lia].
Qed.
'''
s+='Definition captured_register_numbers (v:global_leaves) (index:nat) : Z := nth 0 [::'+ ';'.join(f'to_Zpos(global_word_{idx[":"+str(b)]} v)' for r,m,b,p,k in entries)+'] index.\n'
rows=[(71,12,1),(107,13,1),(144,13,4),(180,12,16),(198,2,64)]
s+='Lemma captured_weight_rows v (sizes:global_leaf_sizes v) : weighted_registers(captured_register_numbers v) = '+ '+'.join(f'{w} * to_Zpos(global_word_{idx[":"+str(p)]} v)' for p,n,w in rows)+'.\nProof.\n'
for p,n,w in rows:
 pi=idx[':'+str(p)]
 s+=f''' have Row{p}:packed_bits {n} (to_Zpos(global_word_{pi} v))=to_Zpos(global_word_{pi} v).
 {{ apply packed_bits_exact. split; [apply to_Zpos_ge0|]. have B:=to_Zpos_bounded(global_word_{pi} v). rewrite (global_size_{pi} v sizes) in B. exact B. }}
'''
s+=' rewrite '+ ' '.join(f'-(Row{p})' for p,n,w in rows)+'.\n unfold weighted_registers,captured_register_numbers. cbn [nth].\n rewrite '+' '.join(f'(capture_integer_{b} v sizes)' for r,m,b,p,k in entries)+'.\n cbn [packed_bits].\n'+'\n'.join(f' change (2 ^ Z.of_nat {k}) with {2**k}.' for k in range(13))+'\n ring.\nQed.\n'
(H/'CaptureNumbers.v').write_text(s)
