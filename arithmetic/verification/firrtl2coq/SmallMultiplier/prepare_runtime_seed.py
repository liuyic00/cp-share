from pathlib import Path
import json
H=Path(__file__).resolve().parent
m=json.loads((H/'stable-nodes.json').read_text());idx=json.loads((H/'global-key-index.json').read_text());regs=m['registers'];byindex={idx[':'+str(r)]:r for r in regs}
widths={idx[':'+str(r)]:m['root_types'][str(r)][1] for r in regs}
widths.update({0:1,1:1,2:8,53:8,56:1,61:1})
s=r'''From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
From ArithmeticCommon Require Import SymbolicInitialFacts HierarchyFacts.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalInstances GlobalProgressTypes GlobalInitialLocal RuntimeState.
Local Open Scope N_scope.
Definition seed_bits (inputs:formal_inputs) (id:N) width := proj1_sig(formal_symbolic_inputs inputs [::] [::0%nat;N.to_nat id] [::] width).
Lemma seed_bits_size inputs id width : size(seed_bits inputs id width)=width.
Proof. exact(proj2_sig(formal_symbolic_inputs inputs [::] [::0%nat;N.to_nat id] [::] width)). Qed.
Definition seed_leaves inputs : global_leaves := fun index=>match N.of_nat index with
'''
for i in range(62):s+=f'| {i}=>'+(f'seed_bits inputs {byindex[i]} {widths[i]}' if i in byindex else f'zeros {widths[i]}')+'\n'
s+='| _=>[::]end.\n'
s+='Lemma seed_registers_expanded inputs env : initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env=\n'
v='env'
for r in regs:v=f'(VM.add {r} (Gval(Fuint {m["root_types"][str(r)][1]})(seed_bits inputs {r} {m["root_types"][str(r)][1]})) {v})'
s+=v+'.\nProof. reflexivity. Qed.\n'
s+='''Lemma seed_registers_match inputs env : multiplier_register_values (seed_leaves inputs) (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env).
Proof. intros index inside.
'''
for i,r in sorted(byindex.items()):
 w=widths[i]
 s+=f''' destruct inside as [same|inside].
 - subst index. change (VM.find {r} (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint {w})(seed_bits inputs {r} {w}))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
'''
s+=' contradiction.\nQed.\n'
s+='''Lemma seed_leaf_sizes inputs : global_leaf_sizes(seed_leaves inputs).
Proof. intros index inside.
 have Member:List.In index (List.seq 0 62) by apply List.in_seq;move/ltP:inside;lia.
 change (List.In index [::'''+ ';'.join(f'{i}%nat' for i in range(62))+''']) in Member.
'''
for i in range(62):
 s+=' destruct Member as [same|Member].\n - subst index. '
 s+=f'exact(seed_bits_size inputs {byindex[i]} {widths[i]}).\n' if i in byindex else 'apply size_zeros.\n'
s+=' contradiction.\nQed.\n'
s+='''Local Opaque circuit_symbolic_initial_state.
Theorem represented_symbolic_initial contents inputs states
 (ran:circuit_symbolic_initial_state generated_modules generated_top contents inputs=Some states) : represented_state states.
Proof.
 destruct (symbolic_initial_local generated_modules generated_top contents inputs states multiplier_instances [::] 3 (multiplier_ports 3) generated_module_3_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) ran) as [env Found].
 exists (seed_leaves inputs),(initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env).
 split;[exact Found|]. split;[apply seed_leaf_sizes|apply seed_registers_match].
Qed.
'''
(H/'RuntimeSeed.v').write_text(s)
