from pathlib import Path
import json,re
H=Path(__file__).resolve().parent
g=json.loads((H/'global-dependencies.json').read_text());idx=json.loads((H/'global-key-index.json').read_text());keys=sorted(idx,key=idx.get);m=json.loads((H/'stable-nodes.json').read_text())
header='''From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import InitialMapFacts InitialInstanceFacts CircuitInitialFacts HierarchyFacts PortFieldFacts.
From SmallMultiplier Require Import Model GlobalStable GlobalInstances GlobalProgressTypes GlobalInitialLocal.
Local Open Scope N_scope.
Local Opaque statements_initial_map_with_memory circuit_initial_map_with_memory.
Lemma multiplier_initial_root v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 exists env,statements_initial_map_with_memory generated_modules generated_module_3_stmts_0
 (match previous with Some maps=>SVM.find [::] maps|None=>None end) (ports_initial_map(multiplier_ports 3))=Some env /\
 SVM.find [::] states=Some(multiplier_externalized v env).
Proof.
 destruct (circuit_initial_root generated_modules generated_top previous external states multiplier_instances (multiplier_ports 3) generated_module_3_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) ran) as [before [after [Initial [External Found]]]].
 rewrite (multiplier_external_update v before external ports) in External. inversion External;subst after.
 exists before;split;assumption.
Qed.
'''
# Avoid Python backslash-newline removal.
header=header.replace('Some env / SVM.find','Some env /\\ SVM.find')
s=header
for k in keys:
 node=g['nodes'].get(k);n=idx[k]
 if not node or node['kind'] not in ['connect','portconnect']:continue
 p,*ids=k.split(':');ids=list(map(int,ids));mid=g['instances'][p];path='[::'+';'.join(reversed(p.split('/')))+']' if p else '[::]'
 s+=f'''Lemma initial_type_{n} v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 option_map type_of_val(global_value_at {n}%nat states)=Some(Gtyp(global_type_at {n}%nat)).
Proof.
'''
 if not p:s+=' destruct (multiplier_initial_root v previous external states ports ran) as [env [Initial Found]].\n'
 else:s+=f''' destruct (circuit_initial_child generated_modules generated_top previous external states multiplier_instances {path} {mid} (multiplier_ports {mid}) generated_module_{mid}_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) (ltac:(discriminate)) ran) as [env [Initial Found]].
'''
 if len(ids)==1:
  s+=f' change (option_map type_of_val(circuit_lookup {path} {ids[0]} states)=Some(Gtyp(global_type_at {n}%nat))).\n'
  s+=' unfold circuit_lookup. rewrite Found.\n'
 else:
  s+=f' change (option_map type_of_val(circuit_interface {path} {ids[0]} {ids[1]} states)=Some(Gtyp(global_type_at {n}%nat))).\n'
  s+=' unfold circuit_interface,circuit_lookup. rewrite Found.\n'
 if not p:s+=f' rewrite (multiplier_external_private v env {ids[0]} (ltac:(reflexivity))).\n'
 s+=f' rewrite (initial_'+('output' if len(ids)==1 else 'bundle')+f'_{mid}_{ids[0]} _ env Initial). reflexivity.\nQed.\n'
(H/'GlobalInitialTypes.v').write_text(s)
s=header
for k in g['leaves']:
 n=idx[k];id=int(k[1:]);kind,w=m['root_types'][str(id)];ty='Fclock' if kind==2 else f'(Fuint {w})'
 s+=f'''Lemma initial_leaf_{n} v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_value_at {n}%nat states=Some(global_target_at {n}%nat v).
Proof.
 destruct (multiplier_initial_root v (Some previous) external states ports ran) as [env [Initial Found]].
 change (circuit_lookup [::] {id} states=Some(Gval {ty} (global_word_{n} v))).
 unfold circuit_lookup. rewrite Found.
'''
 if id in m['inputs']:s+=f' apply multiplier_external_{id}.\n'
 else:
  s+=f''' rewrite (multiplier_external_private v env {id} (ltac:(reflexivity))).
 have Known := registers {n}%nat (ltac:(simpl;tauto)).
 change (VM.find {id} old=Some(Gval {ty} (global_word_{n} v))) in Known.
 cbn beta iota zeta in Initial. rewrite old_found in Initial.
 eapply (initial_register_value generated_modules old {id} _ generated_module_3_stmts_0 Known initial_register_{id}); exact Initial.
'''
 s+='Qed.\n'
s+='''Lemma rank_zero_is_leaf index (inside:(index<2262)%coq_nat) (zero:(global_rank_at index<=0)%coq_nat) : (index<62)%coq_nat.
Proof.
 have Checked: List.forallb (fun n=>if Nat.leb(global_rank_at n)0 then Nat.ltb n 62 else true)(List.seq 0 2262)=true by vm_compute;reflexivity.
 have Member:List.In index (List.seq 0 2262) by apply List.in_seq;lia.
 have Value := (proj1 (List.forallb_forall _ _) Checked) index Member.
 have Zero:Nat.leb(global_rank_at index)0=true by apply Nat.leb_le;exact zero.
 rewrite Zero in Value. apply Nat.ltb_lt. exact Value.
Qed.
Lemma multiplier_initial_ranked v previous old external states
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top (Some previous) external=Some states) :
 global_ranked v 0 states.
Proof.
 intros index inside zero. have Bound:=rank_zero_is_leaf index inside zero.
'''
for n in range(len(g['leaves'])):s+=f' destruct index as [|index]; [exact(initial_leaf_{n} v previous old external states old_found registers ports ran)|].\n'
s+=' lia.\nQed.\n'
(H/'GlobalInitialLeaves.v').write_text(s)
