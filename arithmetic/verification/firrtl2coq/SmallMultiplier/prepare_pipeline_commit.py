#!/usr/bin/env python3
"""Generate the true-edge register bridge from original FIRRTL connections."""
from pathlib import Path
import json,re
P=Path(__file__).resolve().parent;j=json.loads((P/'stable-nodes.json').read_text());idx=json.loads((P/'global-key-index.json').read_text());width={int(k):v[1] for k,v in j['root_types'].items()};regs=j['registers'];model=(P/'Model.v').read_text()
def form(start):
 d=0
 for i in range(start,len(model)):
  d+=(model[i]=='(')-(model[i]==')')
  if d==0:return model[start:i+1]
nexts={}
for id in regs:
 m=re.search(r'\(@Sfcnct VarOrder.T \(@Eid VarOrder.T '+str(id)+r'\) ',model);whole=form(m.start());nexts[id]=whole[m.end()-m.start():-1]
s=['''From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import StatementFacts GroundFrames ConnectionFacts RegisterCommitFacts
 RegisterWriteFacts ScalarEvaluation ScalarExtensionality.
From SmallMultiplier Require Import Model Stable GlobalStable GlobalLookups.
Definition root_domain (id:N) : Prop := N.lt id 421 /\ (N.lt id 7 \/ N.le 37 id).
Local Open Scope N_scope.
Lemma multiplier_resets_inert old : registers_inert
 (fun expr => eval_hfexpr_with_memory empty_memory_map expr old old) generated_module_3_stmts_0.
Proof. cbn [registers_inert generated_module_3_stmts_0]. repeat split; intro proposed; reflexivity. Qed.
''']
for id in regs:
 expr=nexts[id];w=width[id];refs=sorted(set(map(int,re.findall(r'Eid VarOrder.T (\d+)',expr))))
 env='(VM.empty hvalue)'
 for dep in refs:env=f'(VM.add {dep} (Gval (Fuint {width[dep]}) (global_word_{idx[":"+str(dep)]} v)) {env})'
 s.append(f'''Definition next_expr_{id} : @hfexpr VarOrder.T := {expr}.
Definition next_closed_{id} v : VM.t hvalue := {env}.
Definition next_raw_word_{id} v := word_of_eval (eval_hfexpr next_expr_{id} (next_closed_{id} v) (next_closed_{id} v)).
Definition next_word_{id} v := zext_to {w} (take {w} (next_raw_word_{id} v)).
Lemma next_closed_{id}_value v : eval_hfexpr next_expr_{id} (next_closed_{id} v) (next_closed_{id} v) = Some (Gval (Fuint {w}) (next_raw_word_{id} v)).
Proof. unfold next_raw_word_{id}, next_closed_{id}, next_expr_{id}, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_{id}.
Lemma next_expr_{id}_value v : eval_hfexpr next_expr_{id} (global_env_root v) (global_env_root v) = Some (Gval (Fuint {w}) (next_raw_word_{id} v)).
Proof. change (eval_hfexpr next_expr_{id} (next_closed_{id} v) (next_closed_{id} v) = Some (Gval (Fuint {w}) (next_raw_word_{id} v))). apply next_closed_{id}_value. Qed.
Lemma register_write_{id} : register_write_certificate {id} (@Sfcnct VarOrder.T (@Eid VarOrder.T {id}) next_expr_{id}) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_{id} invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find {id} after = Some (Gval (Fuint {w}) (next_word_{id} v)).
Proof.
 have old_found : VM.find {id} old = Some (Gval (Fuint {w}) (global_word_{idx[":"+str(id)]} v)).
 {{ rewrite (agree {id}); [exact (global_lookup_{idx[":"+str(id)]} v)|vm_compute; intuition congruence]. }}
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_{id} old old = Some (Gval (Fuint {w}) (next_raw_word_{id} v)).
 {{ rewrite (scalar_eval_empty_memory next_expr_{id} old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_{id} old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_{id}_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_{id} scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }}
 eapply pass_register_write_value; [exact register_write_{id}|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
''')
 isref=expr.startswith('(@Eref ')
 if isref:
  source=refs[0]
  s.append(f''' eapply bidirectional_eid_target with (value:=Gval (Fuint {w}) (next_raw_word_{id} v)) (source:={source}) (target:={id}) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
''')
 else:
  s.append(f''' eapply unidirectional_eid_target with (expr:=next_expr_{id}) (value:=Gval (Fuint {w}) (next_raw_word_{id} v)) (ground:=Fuint {w}) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old) (set_regs:=true).
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - reflexivity.
 - eapply one_statement_nonref; [reflexivity|exact step].
''')
 s.append('Qed.\n')
s.append('Definition next_register_value v (id:N) : hvalue := match id with\n')
for id in regs:s.append(f' | {id} => Gval (Fuint {width[id]}) (next_word_{id} v)\n')
s.append(' | _ => Needtobedefined (Gtyp (Fuint 0)) end.\n')
s.append('Definition multiplier_committed v (env:VM.t hvalue) := forall id, List.In id [:: '+ '; '.join(map(str,regs))+'] -> VM.find id env = Some (next_register_value v id).\n')
s.append('''Lemma multiplier_commit_values invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 multiplier_committed v after.
Proof. intros id inside.
''')
for id in regs:s.append(f' destruct inside as [same|inside]; [subst id; exact (commit_register_{id} invalid v old before after agree ran)|].\n')
s.append(' contradiction.\nQed.\nPrint Assumptions multiplier_commit_values.\n')
(P/'PipelineCommit.v').write_text(''.join(s))
