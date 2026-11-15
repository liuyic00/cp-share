from pathlib import Path
import json
H=Path(__file__).resolve().parent
g=json.loads((H/'global-dependencies.json').read_text());idx=json.loads((H/'global-key-index.json').read_text());keys=sorted(idx,key=idx.get);count=len(keys)
header='''From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalProgressTypes GlobalFieldSteps GlobalScalarSteps GlobalProgress.
Local Open Scope N_scope.
'''
s=header
for k in keys:
 node=g['nodes'].get(k);n=idx[k]
 if not node or node['kind'] not in ['connect','portconnect']:continue
 s+=f'''Lemma global_type_progress_{n} invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at {n}%nat final) = Some (Gtyp (global_type_at {n}%nat)).
Proof.
 have Typed := types {n}%nat (ltac:(lia)) (Logic.eq_refl true).
'''
 if node['kind']=='portconnect':s+=f' exact (global_field_{n}_type invalid snapshot final Typed ran).\n'
 else:
  s+=' destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].\n'
  s+=f' destruct (global_scalar_{n}_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].\n'
  s+=f' change (option_map type_of_val ('
  p,id=k.split(':');path='[::'+';'.join(reversed(p.split('/')))+']' if p else '[::]'
  s+=f'HierarchyFacts.circuit_lookup {path} {id} final) = Some (Gtyp (global_type_at {n}%nat))).\n'
  s+=' rewrite Result. exact (f_equal Some ResultType).\n'
 s+='Qed.\n'
(H/'GlobalTypeProgress.v').write_text(s)
for chunk,start in enumerate(range(0,count,200)):
 stop=min(start+200,count);s=header+'From SmallMultiplier Require Import GlobalTypeProgress.\n'
 for kind in ['rank','type']:
  params=' v level (prior:global_ranked v level snapshot) (sizes:global_leaf_sizes v)' if kind=='rank' else ''
  prop='(global_rank_at index <= S level)%coq_nat -> global_value_at index final = Some (global_target_at index v)' if kind=='rank' else 'global_port_at index=true -> option_map type_of_val (global_value_at index final)=Some(Gtyp(global_type_at index))'
  s+=f'''Lemma global_{kind}_chunk_{chunk} invalid snapshot final{params}
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 List.Forall (fun index => {prop}) (List.seq {start} {stop-start}).
Proof.
'''
  for n in range(start,stop):
   s+=' constructor.\n'
   if kind=='rank':s+=f' - intro enough. exact (global_progress_{n} invalid snapshot final v level prior types sizes enough ran).\n'
   elif g['nodes'].get(keys[n],{}).get('kind') in ['connect','portconnect']:
    s+=f' - intro included. exact (global_type_progress_{n} invalid snapshot final types ran).\n'
   else:s+=' - intro excluded. discriminate excluded.\n'
  s+=' constructor.\nQed.\n'
 (H/f'GlobalConvergence{chunk}.v').write_text(s)
s=header+'From SmallMultiplier Require Import '+' '.join('GlobalConvergence'+str(c) for c in range((count+199)//200))+'.\n'
s+='''Lemma finite_forall (P:nat->Prop) start count index
 (checked:List.Forall P (List.seq start count))
 (inside:Nat.le start index /\ Nat.lt index (Nat.add start count)) : P index.
Proof. apply (proj1 (List.Forall_forall P _) checked). apply List.in_seq. exact inside. Qed.
'''
for kind in ['rank','type']:
 params=' v level (prior:global_ranked v level snapshot) (sizes:global_leaf_sizes v)' if kind=='rank' else ''
 result='global_ranked v (S level) final' if kind=='rank' else 'global_port_types final'
 s+=f'''Lemma global_{kind}_step invalid snapshot final{params}
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 {result}.
Proof. intros index inside.
'''
 for chunk,start in enumerate(range(0,count,200)):
  stop=min(start+200,count)
  if stop<count:s+=f' destruct (lt_dec index {stop}) as [Range|Range{chunk}].\n - '
  else:s+=' '
  prop='(global_rank_at n <= S level)%coq_nat -> global_value_at n final = Some (global_target_at n v)' if kind=='rank' else 'global_port_at n=true -> option_map type_of_val (global_value_at n final)=Some(Gtyp(global_type_at n))'
  s+=f'exact (finite_forall (fun n => {prop}) {start} {stop-start} index (global_{kind}_chunk_{chunk} invalid snapshot final'+(' v level prior sizes' if kind=='rank' else '')+' types ran) (ltac:(lia))).\n'
 s+='Qed.\n'
s+='''Local Opaque circuit_value_iter_with_memory_policy.
Theorem global_iterations_ranked v inputs count initial final level
 (prior:global_ranked v level initial) (types:global_port_types initial) (sizes:global_leaf_sizes v)
 (ran:circuit_formal_iterations generated_modules generated_top inputs count initial=Some final) :
 global_ranked v (Nat.add count level) final /\ global_port_types final.
Proof.
 revert initial final level prior types ran. induction count as [|count IH]; intros initial final level prior types ran.
 - cbn [circuit_formal_iterations] in ran. inversion ran; subst final. split; assumption.
 - cbn [circuit_formal_iterations] in ran.
   destruct (circuit_value_iter_with_memory_policy (formal_invalid_policy inputs) generated_modules generated_top initial false) as [next|] eqn:Next; [|discriminate].
   have Ranked := global_rank_step _ _ _ v level prior sizes types Next.
   have Typed := global_type_step _ _ _ types Next.
   have Result := IH next final (S level) Ranked Typed ran.
   replace (Nat.add (S count) level) with (Nat.add count (S level)) by lia. exact Result.
Qed.
'''
(H/'GlobalConvergence.v').write_text(s)
