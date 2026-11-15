#!/usr/bin/env python3
from pathlib import Path
import json
H=Path(__file__).resolve().parent;d=json.loads((H/'nodes.json').read_text())
s=['''From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import StatementFacts GroundFrames.
From Divider Require Import Model Stable.
Local Open Scope N_scope.
''']
for k,w in d['widths'].items():
 ty='Fclock' if k=='0' else f'(Fuint {w})'
 s += [f'Lemma target_{k}_value v : VM.find {k} (stable_env v) = Some (Gval {ty} (word_{k} v)).','Proof. reflexivity. Qed.']
for k in d['inputs']:
 s += [f'Lemma input_{k}_frame : flat_sequence_frames {k} generated_module_0_stmts_0 = true.', 'Proof. vm_compute. reflexivity. Qed.', f'Lemma input_{k}_not_register : registers_frame {k} generated_module_0_stmts_0 = true.', 'Proof. vm_compute. reflexivity. Qed.']
for k in d['registers']:
 s += [f'Lemma register_{k}_certificate : flat_register_certificate {k} generated_module_0_stmts_0.', 'Proof. unfold generated_module_0_stmts_0.', ' repeat first [apply flat_register_here; vm_compute; reflexivity | apply flat_register_later; [reflexivity|]]. Qed.']
for k in [2,8,9]:
 s += [f'Lemma output_{k}_certificate : framed_write_certificate {k} (@Sfcnct VarOrder.T (@Eid VarOrder.T {k}) expr_{k}) generated_module_0_stmts_0.',f'Proof. unfold generated_module_0_stmts_0, expr_{k}.', ' repeat first [apply framed_write_here; vm_compute; reflexivity | apply framed_write_later; [vm_compute; reflexivity|]]. Qed.',f'Lemma output_{k}_not_register : registers_frame {k} generated_module_0_stmts_0 = true.', 'Proof. vm_compute. reflexivity. Qed.']
s+=['Print Assumptions output_9_certificate.'];(H/'Frames.v').write_text('\n'.join(s)+'\n')
