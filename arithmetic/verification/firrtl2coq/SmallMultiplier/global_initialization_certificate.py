from pathlib import Path
import json
H=Path(__file__).resolve().parent
g=json.loads((H/'global-dependencies.json').read_text());idx=json.loads((H/'global-key-index.json').read_text());m=json.loads((H/'stable-nodes.json').read_text())
header='''From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import InitialMapFacts InitialInstanceFacts CircuitInitialFacts HierarchyFacts PortFieldFacts.
From SmallMultiplier Require Import Model GlobalStable GlobalInstances GlobalProgressTypes.
Local Open Scope N_scope.
'''
s=header
for mid in range(4):
 ports=m['ports'][str(mid)]
 for id,d,kind,w in ports:
  if d!='output':continue
  s+=f'''Lemma initial_output_{mid}_{id} previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_{mid}_stmts_0 previous (ports_initial_map(multiplier_ports {mid}))=Some env) :
 VM.find {id} env=Some(Needtobedefined(Gtyp(Fuint {w}))).
Proof.
 rewrite (initial_sequence_preserves generated_modules previous {id} generated_module_{mid}_stmts_0 (ports_initial_map(multiplier_ports {mid})) env (ltac:(vm_compute;reflexivity)) ran).
 reflexivity.
Qed.
'''
 inst=m['instances'] if mid==3 else {'10':1,'11':1} if mid==2 else {}
 for id,child in inst.items():
  s+=f'''Lemma initial_instance_{mid}_{id} : initial_instance_certificate {id} {child} generated_module_{mid}_stmts_0.
Proof. apply checked_initial_instance_sound. vm_compute. reflexivity. Qed.
Definition instance_type_{mid}_{id} := Eval vm_compute in match module_type generated_modules {child} with Some t=>t|None=>Gtyp(Fuint 0)end.
Lemma initial_bundle_{mid}_{id} previous env
 (ran:statements_initial_map_with_memory generated_modules generated_module_{mid}_stmts_0 previous (ports_initial_map(multiplier_ports {mid}))=Some env) :
 VM.find {id} env=Some(Needtobedefined instance_type_{mid}_{id}).
Proof. eapply (initial_instance_value generated_modules previous {id} {child} instance_type_{mid}_{id} generated_module_{mid}_stmts_0); [reflexivity|exact initial_instance_{mid}_{id}|exact ran]. Qed.
'''
for id in m['registers']:
 s+=f'''Lemma initial_register_{id} : initial_register_certificate {id} generated_module_3_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
'''
s+='''Definition multiplier_register_values (v:global_leaves) env := forall index, List.In index [::'''+ ';'.join(str(idx[':'+str(id)])+'%nat' for id in m['registers'])+'''] -> global_value_at index (SVM.add [::] env (SVM.empty(VM.t hvalue)))=Some(global_target_at index v).
Definition multiplier_input_values (v:global_leaves) external := '''
s+=' /\\ '.join(f'VM.find {id} external=Some(Gval '+('Fclock' if id==0 else '(Fuint 8)' if id in [2,3] else '(Fuint 1)')+f' (global_word_{idx[":"+str(id)]} v))' for id in m['inputs'])+'.\n'
s+='Definition multiplier_externalized v env := '
exp='env'
for id in m['inputs']:
 typ='Fclock' if id==0 else '(Fuint 8)' if id in [2,3] else '(Fuint 1)'
 exp=f'(VM.add {id} (Gval {typ} (global_word_{idx[":"+str(id)]} v)) {exp})'
s+=exp+'.\n'
s+='''Lemma multiplier_external_update v declared external (ports:multiplier_input_values v external) :
 update_external_ports declared external (multiplier_ports 3)=Some(multiplier_externalized v declared).
Proof. destruct ports as [E0 [E1 [E2 [E3 [E4 E5]]]]].
 change (update_external_ports declared external [::@Finput VarOrder.T 0 (Gtyp Fclock);@Finput VarOrder.T 1 (Gtyp(Fuint 1));@Finput VarOrder.T 2 (Gtyp(Fuint 8));@Finput VarOrder.T 3 (Gtyp(Fuint 8));@Finput VarOrder.T 4 (Gtyp(Fuint 1));@Finput VarOrder.T 5 (Gtyp(Fuint 1));@Foutput VarOrder.T 6 (Gtyp(Fuint 16))]=Some(multiplier_externalized v declared)).
 cbn [update_external_ports is_passive]. rewrite E0 E1 E2 E3 E4 E5. reflexivity.
Qed.
'''
# All ids except external input ids are unchanged in the root external update.
s+='''Lemma multiplier_external_private v env id (private:(5 < id)%num) :
 VM.find id (multiplier_externalized v env)=VM.find id env.
Proof.
 unfold multiplier_externalized.
 repeat (rewrite VM.Lemmas.find_add_neq; [|intro Same; move/eqP:Same=>Same; subst id; discriminate private]). reflexivity.
Qed.
'''
for id in m['inputs']:
 typ='Fclock' if id==0 else '(Fuint 8)' if id in [2,3] else '(Fuint 1)'
 s+=f'''Lemma multiplier_external_{id} v env : VM.find {id} (multiplier_externalized v env)=Some(Gval {typ} (global_word_{idx[":"+str(id)]} v)).
Proof. unfold multiplier_externalized.
 repeat first [rewrite VM.Lemmas.find_add_eq; [reflexivity|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. Qed.
'''
(H/'GlobalInitialLocal.v').write_text(s)
