from pathlib import Path
H=Path(__file__).resolve().parent
s=r'''From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Stable GlobalStable GlobalWidths PipelineCommit PipelineEquations.
Local Open Scope N_scope.
Lemma one_bit_word (word:bits) (sized:size word=1%nat) : exists b,word=[::b].
Proof. destruct word as [|b tail]; [discriminate|]. destruct tail; [exists b;reflexivity|discriminate]. Qed.
'''
s+='Local Opaque '+' '.join('global_word_'+str(i) for i in range(2262))+'.\n'
for reg, nodes,expr in [(410,[1298],'andb (negb reset) (orb enable valid)'),(419,[1305,1304],'andb (negb reset) (andb valid (negb enable))')]:
 s+=f'''Local Transparent next_raw_word_{reg} '''+' '.join(f'global_word_{n}' for n in nodes)+f'''.
Lemma control_next_{reg} v reset enable valid
 (R:global_word_1 v=[::reset]) (E:global_word_56 v=[::enable]) (V:global_word_58 v=[::valid]) :
 next_word_{reg} v=[::{expr}].
Proof.
 unfold next_word_{reg},next_raw_word_{reg},next_expr_{reg},next_closed_{reg}.
'''
 s+=' unfold '+','.join(f'global_word_{n},global_expr_{n},global_closed_{n}' for n in nodes)+'.\n'
 s+=' rewrite R E V. destruct reset,enable,valid; vm_compute; reflexivity.\nQed.\n'
 s+='Local Opaque '+' '.join(f'global_word_{n}' for n in nodes)+'.\n'
s+=r'''Local Transparent global_word_1297 next_raw_word_408 next_raw_word_416.
Lemma expected_mux v (sizes:global_leaf_sizes v) : global_word_1297 v=
 if is_zero(global_word_56 v) then global_word_57 v else global_word_1296 v.
Proof.
 unfold global_word_1297,global_expr_1297,global_closed_1297,word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 have TS:eval_type_of_expr (@Eref VarOrder.T (@Eid VarOrder.T 407)) (global_closed_1297 v)=Some(Gtyp(Fuint 16)) by reflexivity.
 have TR:eval_type_of_expr (@Eref VarOrder.T (@Eid VarOrder.T 408)) (global_closed_1297 v)=Some(Gtyp(Fuint 16)) by reflexivity.
 rewrite TS TR. destruct (is_zero(global_word_56 v)).
 - change (zext_to 16 (take 16 (global_word_57 v))=global_word_57 v). apply register_adapt_identity. exact(global_size_57 v sizes).
 - change (zext_to 16 (take 16 (global_word_1296 v))=global_word_1296 v). apply register_adapt_identity. exact(global_size_1296 v sizes).
Qed.
Local Opaque global_word_1297.
Lemma expected_next v (sizes:global_leaf_sizes v) : next_word_408 v=
 if is_zero(global_word_56 v) then global_word_57 v else global_word_1296 v.
Proof.
 unfold next_word_408,next_raw_word_408,next_expr_408,next_closed_408,word_of_eval.
 cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; [|reflexivity].
 change (zext_to 16 (take 16(global_word_1297 v)) = if is_zero(global_word_56 v) then global_word_57 v else global_word_1296 v).
 rewrite register_adapt_identity; [exact(expected_mux v sizes)|exact(global_size_1297 v sizes)].
Qed.
Lemma previous_next v (sizes:global_leaf_sizes v) : next_word_416 v=global_word_1299 v.
Proof.
 unfold next_word_416,next_raw_word_416,next_expr_416,next_closed_416,word_of_eval.
 cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; [|reflexivity].
 change (zext_to 16 (take 16(global_word_1299 v))=global_word_1299 v).
 apply register_adapt_identity. exact(global_size_1299 v sizes).
Qed.
'''
(H/'ControlEquations.v').write_text(s)
