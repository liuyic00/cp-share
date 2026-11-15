#!/usr/bin/env python3
from pathlib import Path
import re,runpy
H=Path(__file__).resolve().parent
x=runpy.run_path(str(H/'stable_certificate.py'));model=x['model'];form=x['form']
out=['From Coq Require Import NArith.','From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.','From simplssrlib Require Import Types SsrOrder Var.','From nbits Require Import NBits.','From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.','From ArithmeticCommon Require Import StatementFacts PortFieldFacts FieldStatementFacts FieldTypes FieldConnections FieldTypePreservation.','From SmallMultiplier Require Import Model FieldCertificateCheck.','Local Open Scope N_scope.']
count=0
for mid in [2,3]:
 body=model.split(f'Definition generated_module_{mid}_stmts_0')[1].split(f'Definition generated_module_{mid} :')[0]
 for m in re.finditer(r'\(@Sfcnct VarOrder.T ',body):
  f=form(body,m.start());r=form(f,m.end()-m.start());expr=f[m.end()-m.start()+len(r)+1:-1]
  port=re.fullmatch(r'\(@Esubfield VarOrder.T \(@Eid VarOrder.T (\d+)\) (\d+)\)',r)
  if not port:continue
  inst,field=map(int,port.groups());name=f'field_{mid}_{inst}_{field}';count+=1
  out +=[f'Definition {name}_rhs : @hfexpr VarOrder.T := {expr}.',f'Lemma {name}_certificate : field_write_certificate {inst} {field} (@Sfcnct VarOrder.T {r} {name}_rhs) generated_module_{mid}_stmts_0.','Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.',f'''Lemma {name}_type invalid old before after ground
 (initial_type : eval_type_of_ref {r} before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_{mid}_stmts_0 = Some after) :
 eval_type_of_ref {r} after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact {name}_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma {name}_value invalid old before after ground value bits initial
 (initial_field : interface_field {inst} {field} before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map {name}_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_{mid}_stmts_0 = Some after) :
 interface_field {inst} {field} after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact {name}_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.''']
(H/'FieldWrites.v').write_text('\n'.join(out)+'\n')
print(count,'original bundle-field writers')
