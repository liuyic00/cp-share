from pathlib import Path
import json,re
H=Path(__file__).resolve().parent
idx=json.loads((H/'global-key-index.json').read_text())
entries=[tuple(map(int,x)) for x in re.findall(r'Build_capture_entry (\d+) (\d+) (\d+) (\d+) (\d+)',(H/'CaptureAST.v').read_text())]
s=r'''From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Stable GlobalStable GlobalWidths PipelineCommit RuntimeWords.
Local Open Scope N_scope.
Lemma register_adapt_identity width word (sized:size word=width) : zext_to width (take width word)=word.
Proof. rewrite -sized take_size. unfold zext_to. rewrite subnn /zext cats0. reflexivity. Qed.
'''
s+='Local Opaque '+' '.join('global_word_'+str(n) for n in range(2262))+'.\n'
for r,m,b,p,k in entries:
 ri,mi,bi=[idx[':'+str(x)] for x in (r,m,b)]
 s+=f'''Local Transparent global_word_{mi} next_raw_word_{r}.
Lemma capture_mux_{r} v (sizes:global_leaf_sizes v) : global_word_{mi} v = if is_zero(global_word_56 v) then global_word_{ri} v else global_word_{bi} v.
Proof.
 unfold global_word_{mi},global_closed_{mi},global_expr_{mi},word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 have SourceType: eval_type_of_expr (@Eref VarOrder.T (@Eid VarOrder.T {b})) (global_closed_{mi} v)=Some(Gtyp(Fuint 1)) by reflexivity.
 have RegisterType: eval_type_of_expr (@Eref VarOrder.T (@Eid VarOrder.T {r})) (global_closed_{mi} v)=Some(Gtyp(Fuint 1)) by reflexivity.
 rewrite SourceType RegisterType.
 destruct (is_zero (global_word_56 v)).
 - change (zext_to 1 (take 1 (global_word_{ri} v))=global_word_{ri} v).
   apply register_adapt_identity. exact(global_size_{ri} v sizes).
 - change (zext_to 1 (take 1 (global_word_{bi} v))=global_word_{bi} v).
   apply register_adapt_identity. exact(global_size_{bi} v sizes).
Qed.
Local Opaque global_word_{mi}.
Lemma capture_next_{r} v (sizes:global_leaf_sizes v) : next_word_{r} v = if is_zero(global_word_56 v) then global_word_{ri} v else global_word_{bi} v.
Proof.
 unfold next_word_{r},next_raw_word_{r},next_expr_{r},next_closed_{r},word_of_eval.
 cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; [|reflexivity].
 change (zext_to 1 (take 1 (global_word_{mi} v)) = if is_zero(global_word_56 v) then global_word_{ri} v else global_word_{bi} v).
 rewrite register_adapt_identity; [exact(capture_mux_{r} v sizes)|exact(global_size_{mi} v sizes)].
Qed.
'''
(H/'PipelineEquations.v').write_text(s)
