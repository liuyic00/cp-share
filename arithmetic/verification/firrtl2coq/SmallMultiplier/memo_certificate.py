#!/usr/bin/env python3
from pathlib import Path
import runpy
H=Path(__file__).resolve().parent
c=runpy.run_path(str(H/'stable_certificate.py'));nodes=c['nodes'];refs=c['refs'];typ=c['typ']
selected=[k for k in c['ordered'] if k[0]==0 and 37<=k[1]<=198]
lines=['''From Coq Require Import ZArith NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths.
From SmallMultiplier Require Import Stable.
Local Open Scope N_scope.
''']
for k in selected:
 i=k[1];ds=refs(nodes[k]); assert all(d[0]==0 for d in ds)
 args=' '.join(f'(d{d[1]} : bits)' for d in ds);call=' '.join(f'(word_{d[1]} v)' for d in ds)
 env='(VM.empty hvalue)'
 for d in ds:env=f'(VM.add {d[1]} (Gval {typ(d)} d{d[1]}) {env})'
 lines +=[f'Definition op_{i} {args} : bits := let env := {env} in word_of_eval (eval_hfexpr expr_word_{i} env env).',f'Lemma word_{i}_op v : word_{i} v = op_{i} {call}.',f'Proof. unfold op_{i}, word_{i}, closed_word_{i}. reflexivity. Qed.']
lines += ['Opaque '+' '.join('op_'+str(k[1]) for k in selected)+'.','Definition memo_front (v : leaf_values) :=',' let d2 := word_2 v in let d3 := word_3 v in']
for k in selected:
 i=k[1];ds=refs(nodes[k]);lines +=[f' let d{i} := op_{i} '+ ' '.join('d'+str(d[1]) for d in ds)+' in']
lines += [' (d71,d107,d144,d180,d198).', 'Theorem memo_front_correct v : memo_front v = (word_71 v,word_107 v,word_144 v,word_180 v,word_198 v).', 'Proof. unfold memo_front. cbn zeta.']
for k in selected:lines +=[f' rewrite -?word_{k[1]}_op.']
lines += [' reflexivity. Qed.', 'Transparent '+' '.join('op_'+str(k[1]) for k in selected)+'.','Print Assumptions memo_front_correct.']
(H/'Memo.v').write_text('\n'.join(lines)+'\n')
