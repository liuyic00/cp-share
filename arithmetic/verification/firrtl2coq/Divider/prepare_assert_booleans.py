#!/usr/bin/env python3
from pathlib import Path
import re
P=Path(__file__).resolve().parent;raw=(P.parent/'Generated/Radix2Divider/Model.v').read_text()
guards=[[(8,1),(18,1),(423,1)],[(8,1),(18,1),(428,1)],[(8,1),(18,0),(432,1)],[(8,1),(18,0),(439,1)],[(8,1),(18,0),(443,1)],[(445,1),(448,1),(451,1)],[(445,1),(453,1),(456,1)],[(445,1),(458,1),(463,1)],[(445,1),(458,1),(471,1)],[(475,1),(478,1)],[(475,1),(482,1)]]
s=['''From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From Divider Require Import Model.
From Divider Require Import Model Stable Frames Representation Typing AssertTransfer.
Local Open Scope N_scope.
Lemma one_bit_as_bool (bits : seq bool) (sized : size bits = 1%nat) : exists bit, bits = [::bit].
Proof. destruct bits as [|bit tail]; [discriminate|]. destruct tail; [exists bit; reflexivity|discriminate]. Qed.
Lemma generated_reference_truth env id bits
 (found : VM.find id env = Some (Gval (Fuint 1) bits)) (sized : size bits = 1%nat) :
 Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T id)) env <-> to_Zpos bits = 1%Z.
Proof.
 destruct (one_bit_as_bool bits sized) as [bit E]. subst bits.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href]. rewrite found.
 destruct bit; vm_compute; split; intro H; try discriminate; reflexivity.
Qed.
''']
for id,conditions in enumerate(guards):
 m=re.search(r'Definition generated_assert_m0_'+str(id)+r'_local .*? := generated_expr_true (.*?) sem -> generated_expr_true (.*?) sem\.',raw);guard,pred=m.groups();pid=int(re.search(r'Eid VarOrder.T (\d+)',pred)[1])
 s.append(f'''Lemma assertion_{id}_predicate_integer s i ghost :
 Tool.generated_expr_true {pred} (stable_env (encoded_leaves s i ghost)) <->
 to_Zpos (word_{pid} (encoded_leaves s i ghost)) = 1%Z.
Proof. eapply generated_reference_truth; [exact (target_{pid}_value _)|apply encoded_word_{pid}_size]. Qed.
Lemma assertion_{id}_guard_integers s i ghost :
 Tool.generated_expr_true {guard} (stable_env (encoded_leaves s i ghost)) <->
''')
 s.append(' /\\\n'.join(f' to_Zpos (word_{dep} (encoded_leaves s i ghost)) = {value}%Z' for dep,value in conditions)+'.\nProof.\n')
 for dep,value in conditions:s.append(f' destruct (one_bit_as_bool _ (encoded_word_{dep}_size s i ghost)) as [bit{dep} E{dep}].\n')
 s.append(' unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].\n')
 s.append(' rewrite '+ ' '.join(f'(target_{dep}_value _)' for dep,val in conditions)+'.\n')
 s.append(' rewrite '+ ' '.join('E'+str(dep) for dep,val in conditions)+'.\n')
 s.append(' destruct '+ ', '.join('bit'+str(dep) for dep,val in conditions)+'; vm_compute; intuition discriminate.\nQed.\n')
s.append('Print Assumptions assertion_10_guard_integers.\n')
(P/'AssertBooleans.v').write_text(''.join(s))
