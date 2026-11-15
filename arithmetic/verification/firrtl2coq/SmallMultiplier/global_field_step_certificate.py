#!/usr/bin/env python3
from pathlib import Path
import runpy
H=Path(__file__).resolve().parent;x=runpy.run_path(str(H/'global_lookup_certificate.py'));g=x['g'];idx=x['idx'];typ=x['typ'];path=x['path']
out=['From Coq Require Import NArith.','From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.','From simplssrlib Require Import Types SsrOrder Var.','From nbits Require Import NBits.','From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.','From ArithmeticCommon Require Import HierarchyFacts PortFieldFacts FieldTypes.','From SmallMultiplier Require Import Model GlobalStable GlobalLocal GlobalMemory GlobalInstances GlobalFieldFacts InstanceChecks FieldWrites.','Local Open Scope N_scope.']
count=0
for k in g['order']:
 node=g['nodes'][k]
 if node['kind']!='portconnect':continue
 n=idx[k];p,inst,field=k.split(':');mid=g['instances'][p];scope=path(p);gt=typ(k);cert=f'field_{mid}_{inst}_{field}_certificate';count+=1
 out +=[f'Lemma global_field_{n}_sync : field_sync_check generated_modules multiplier_instances {scope} {inst} {field} = true.','Proof. vm_compute. reflexivity. Qed.',f'''Lemma global_field_{n}_type invalid snapshot final
 (initial_type : option_map type_of_val (circuit_interface {scope} {inst} {field} snapshot) = Some (Gtyp {gt}))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 option_map type_of_val (circuit_interface {scope} {inst} {field} final) = Some (Gtyp {gt}).
Proof. eapply circuit_pass_field_type with (instances:=multiplier_instances) (module_id:={mid}) (ports:=multiplier_ports {mid}) (stmts:=generated_module_{mid}_stmts_0) (rhs:=global_expr_{n}).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact {cert}.
 - vm_compute. reflexivity.
 - exact initial_type.
 - reflexivity.
 - exact global_field_{n}_sync.
 - exact ran.
Qed.''',f'Lemma global_field_{n}_step invalid snapshot final v initial']
 for j,d in enumerate(node['deps']):
  dp,*r=d.split(':');read=f'circuit_lookup {path(dp)} {r[0]} snapshot' if len(r)==1 else f'circuit_interface {path(dp)} {r[0]} {r[1]} snapshot'
  out +=[f' (H{j} : {read} = Some (Gval {typ(d)} (global_word_{idx[d]} v)))']
 out +=[f''' (initial_field : circuit_interface {scope} {inst} {field} snapshot = Some initial)
 (initial_type : type_of_val initial = Gtyp {gt})
 (adapted : adapt_hvalue_as_type (Gval {gt} (global_word_{n} v)) (Gtyp {gt}) = Some (Gval {gt} (global_word_{n} v)))
 (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :
 circuit_interface {scope} {inst} {field} final = Some (Gval {gt} (global_word_{n} v)).
Proof. eapply circuit_pass_field_value with (instances:=multiplier_instances) (module_id:={mid}) (ports:=multiplier_ports {mid}) (stmts:=generated_module_{mid}_stmts_0) (rhs:=global_expr_{n}) (initial:=initial).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact {cert}.
 - vm_compute. reflexivity.
 - exact initial_field.
 - exact initial_type.
 - intros old found. rewrite global_memory_{n}. apply global_local_{n}.''']
 for j,d in enumerate(node['deps']):
  _,*r=d.split(':')
  if len(r)==1:out +=[f'   + unfold circuit_lookup in H{j}. rewrite found in H{j}. exact H{j}.']
  else:out +=[f'   + unfold circuit_interface, circuit_lookup in H{j}. rewrite found in H{j}. rewrite interface_field_eval. exact H{j}.']
 out +=[' - exact adapted.',' - reflexivity.',f' - exact global_field_{n}_sync.',' - exact ran.','Qed.']
(H/'GlobalFieldSteps.v').write_text('\n'.join(out)+'\n');print(count,'global original field steps')
