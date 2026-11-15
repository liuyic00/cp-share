from pathlib import Path
import json
H=Path(__file__).resolve().parent
g=json.loads((H/'global-dependencies.json').read_text());idx=json.loads((H/'global-key-index.json').read_text());keys=sorted(idx,key=idx.get);count=len(keys)
header='''From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model GlobalStable GlobalInstances GlobalProgressTypes GlobalInitialLocal GlobalInitialTypes.
Local Open Scope N_scope.
'''
for chunk,start in enumerate(range(0,count,200)):
 stop=min(start+200,count);s=header
 s+=f'''Lemma global_initial_type_chunk_{chunk} v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 forall index,(Nat.le {start} index /\ Nat.lt index {stop}) ->
 global_port_at index=true -> option_map type_of_val(global_value_at index states)=Some(Gtyp(global_type_at index)).
Proof.
 intros index Range.
 remember (Nat.sub index {start}) as offset eqn:Offset.
 have Index:index=Nat.add {start} offset by lia.
 have Bound:(offset < {stop-start})%coq_nat by lia.
 rewrite Index.
'''
 for n in range(start,stop):
  s+=' destruct offset as [|offset].\n'
  if g['nodes'].get(keys[n],{}).get('kind') in ['connect','portconnect']:s+=f' - intro included. exact(initial_type_{n} v previous external states ports ran).\n'
  else:s+=' - intro excluded. discriminate excluded.\n'
 s+=' exfalso;lia.\nQed.\n'
 (H/f'GlobalInitialAll{chunk}.v').write_text(s)
s=header+'From SmallMultiplier Require Import '+' '.join('GlobalInitialAll'+str(c) for c in range((count+199)//200))+'.\n'
s+='''Theorem multiplier_initial_types v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 global_port_types states.
Proof. intros index inside.
'''
for chunk,start in enumerate(range(0,count,200)):
 stop=min(start+200,count)
 if stop<count:s+=f' destruct (lt_dec index {stop}) as [Range|Range{chunk}].\n - '
 else:s+=' '
 s+=f'apply (global_initial_type_chunk_{chunk} v previous external states ports ran index);lia.\n'
s+='Qed.\n'
(H/'GlobalInitialization.v').write_text(s)
