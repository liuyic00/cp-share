From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
From ArithmeticCommon Require Import CircuitInitialFacts InstanceFoldFacts.
Definition create_symbolic_module modules contents inputs initial path module_id :=
 match SVM.find path initial,find_module modules module_id with
 | Some env,Some(FInmod _ _ stmts)=>Some(initialize_symbolic_registers inputs path stmts (initialize_module_memories contents path stmts env))
 | _,_=>None end.
Lemma symbolic_initial_local modules top contents inputs final instances path module_id ports stmts
 (instances_found:find_circuit_instances modules top=Some instances)
 (instance_found:SVM.find path instances=Some module_id)
 (module_found:find_module modules module_id=Some(FInmod module_id ports stmts))
 (ran:circuit_symbolic_initial_state modules top contents inputs=Some final) :
 exists env,SVM.find path final=Some(initialize_symbolic_registers inputs path stmts env).
Proof.
 unfold circuit_symbolic_initial_state in ran. rewrite instances_found in ran.
 destruct (circuit_initial_map_with_memory modules top None(formal_external_inputs inputs)) as [initial|] eqn:Initial;[|discriminate].
 have Same:forall path module_id acc,
 (match acc,SVM.find path initial,find_module modules module_id with
 | Some states,Some env,Some(FInmod _ _ body)=>Some(SVM.add path (initialize_symbolic_registers inputs path body (initialize_module_memories contents path body env)) states)
 | _,_,_=>None end)=create_instance _ _ (create_symbolic_module modules contents inputs initial) path module_id acc.
 { intros p m acc. unfold create_instance,create_symbolic_module.
   destruct acc;destruct(SVM.find p initial);destruct(find_module modules m) as [md|];try reflexivity;destruct md;reflexivity. }
 rewrite (instance_fold_ext _ _ _ _ _ _ Same) in ran.
 destruct (create_fold_lookup _ _ (create_symbolic_module modules contents inputs initial) instances initial final path module_id instance_found ran) as [value [Created Found]].
 unfold create_symbolic_module in Created. rewrite module_found in Created.
 destruct (SVM.find path initial) as [env|];[|discriminate].
 inversion Created;subst value. eexists. exact Found.
Qed.
