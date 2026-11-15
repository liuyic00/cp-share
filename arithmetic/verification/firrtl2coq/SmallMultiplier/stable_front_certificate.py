#!/usr/bin/env python3
from pathlib import Path
import runpy
H=Path(__file__).resolve().parent
x=runpy.run_path(str(H/'stable_certificate.py'))
out=['From Coq Require Import NArith.','From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.','From simplssrlib Require Import Types SsrOrder Var.','From nbits Require Import NBits.','From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.','From ArithmeticCommon Require Import StatementFacts ScalarEvaluation.','From SmallMultiplier Require Import Model Stable PassCertificates LocalEnvironment.','Local Open Scope N_scope.','Section StableFront.','Variable (v : leaf_values) (env : VM.t hvalue) (invalid : invalid_value_policy).','Hypothesis fixed : value_iter_with_memory_policy invalid empty_memory_map env false env generated_module_3_stmts_0 = Some env.','Hypothesis Ha : VM.find 2 env = Some (Gval (Fuint 8) (word_2 v)).','Hypothesis Hb : VM.find 3 env = Some (Gval (Fuint 8) (word_3 v)).']
for k in x['ordered']:
 if k[0] or not 37<=k[1]<=198:continue
 n=k[1];ds=x['refs'](x['nodes'][k]);t=x['typ'](k)
 out += [f'Lemma stable_word_{n} : VM.find {n} env = Some (Gval {t} (word_{n} v)).',f'Proof. eapply stable_node_value with (expr:=expr_word_{n}); [exact pass_node_{n}_certificate|vm_compute;reflexivity| |exact fixed].',f' rewrite scalar_eval_memory_irrelevant; [|reflexivity]. apply local_word_{n}_value.']
 for d in ds:out+=[' exact '+('Ha' if d[1]==2 else 'Hb' if d[1]==3 else f'stable_word_{d[1]}')+'.']
 out+=['Qed.']
out+=['End StableFront.']
(H/'StableFront.v').write_text('\n'.join(out)+'\n')
