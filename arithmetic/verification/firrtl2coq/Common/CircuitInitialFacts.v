From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import InstanceFoldFacts.
Section Creation.
Variables (Job Value:Type) (create:SVM.key->Job->option Value).
Definition create_instance path job (acc:option(SVM.t Value)) :=
 match acc,create path job with Some states,Some value=>Some(SVM.add path value states)|_,_=>None end.
Lemma create_fold_lookup jobs initial final focus job
 (found:SVM.find focus jobs=Some job)
 (ran:SVM.fold create_instance jobs (Some initial)=Some final) :
 exists value,create focus job=Some value /\ SVM.find focus final=Some value.
Proof.
 eapply (fold_establishes_at_key Job (SVM.t Value) jobs create_instance initial focus
 (fun states=>exists value,create focus job=Some value /\ SVM.find focus states=Some value)); [| | |exact ran|exact found].
 - intros; reflexivity.
 - intros actual before after Actual Ran. rewrite found in Actual. inversion Actual; subst actual.
   unfold create_instance in Ran. destruct (create focus job) as [value|] eqn:Created; [|discriminate].
   inversion Ran; subst after. exists value. split; [reflexivity|apply SVM.Lemmas.find_add_eq; reflexivity].
 - intros path actual before after Actual Different [value [Created Before]] Ran.
   unfold create_instance in Ran. destruct (create path actual) as [other|]; [|discriminate].
   inversion Ran; subst after. exists value. split; [exact Created|].
   rewrite SVM.Lemmas.find_add_neq; [exact Before|]. intro Same. move/eqP:Same=>Same. apply Different. symmetry;exact Same.
Qed.
End Creation.
Definition create_initial_module modules previous path module_id :=
 match find_module modules module_id with
 | Some(FInmod _ ports stmts)=>statements_initial_map_with_memory modules stmts
   (match previous with Some states=>SVM.find path states|None=>None end) (ports_initial_map ports)
 | _=>None end.
Lemma original_initial_create modules previous path module_id acc :
 (match acc with Some partial=>match module_initial_map_with_memory modules path module_id previous partial with Some next=>Some next|None=>None end|None=>None end) =
 create_instance _ _ (create_initial_module modules previous) path module_id acc.
Proof.
 unfold module_initial_map_with_memory,create_instance,create_initial_module.
 destruct acc as [states|]; [|reflexivity].
 destruct (find_module modules module_id) as [m|]; [destruct m as [id ports stmts|]|]; try reflexivity.
 destruct (statements_initial_map_with_memory modules stmts
 (match previous with Some states=>SVM.find path states|None=>None end) (ports_initial_map ports)); reflexivity.
Qed.
Lemma circuit_initial_local modules top previous external states instances
 (instances_found:find_circuit_instances modules top=Some instances)
 (ran:circuit_initial_map_with_memory modules top previous external=Some states) :
 exists declared top_before top_after module_id ports body,
 SVM.find [::] declared=Some top_before /\ find_module modules top=Some(FInmod module_id ports body) /\
 update_external_ports top_before external ports=Some top_after /\ states=SVM.add [::] top_after declared /\
 (forall path module_id, SVM.find path instances=Some module_id -> exists env,
 create_initial_module modules previous path module_id=Some env /\ SVM.find path declared=Some env).
Proof.
 unfold circuit_initial_map_with_memory in ran. rewrite instances_found in ran.
 rewrite (instance_fold_ext _ _ _ _ _ _ (original_initial_create modules previous)) in ran.
 destruct (SVM.fold (create_instance _ _ (create_initial_module modules previous)) instances (Some(SVM.empty(VM.t hvalue)))) as [declared|] eqn:Declared; [|discriminate].
 destruct (SVM.find [::] declared) as [top_before|] eqn:Top; [|discriminate].
 destruct (find_module modules top) as [m|] eqn:Module; [|discriminate].
 destruct m as [module_id ports body|]; [|discriminate].
 destruct (update_external_ports top_before external ports) as [top_after|] eqn:External; [|discriminate].
 inversion ran; subst states.
 exists declared,top_before,top_after,module_id,ports,body.
 split; [exact Top|]. split; [reflexivity|]. split; [exact External|]. split; [reflexivity|].
 intros path id Found. eapply create_fold_lookup; eassumption.
Qed.
Lemma circuit_initial_root modules top previous external states instances ports body
 (instances_found:find_circuit_instances modules top=Some instances)
 (top_found:SVM.find [::] instances=Some top)
 (module_found:find_module modules top=Some(FInmod top ports body))
 (ran:circuit_initial_map_with_memory modules top previous external=Some states) :
 exists before after,
 statements_initial_map_with_memory modules body
 (match previous with Some maps=>SVM.find [::] maps|None=>None end) (ports_initial_map ports)=Some before /\
 update_external_ports before external ports=Some after /\ SVM.find [::] states=Some after.
Proof.
 destruct (circuit_initial_local _ _ _ _ _ _ instances_found ran) as [declared [top_before [top_after [actual [actual_ports [actual_body [Top [Module [External [States Local]]]]]]]]]].
 rewrite module_found in Module. inversion Module; subst actual actual_ports actual_body.
 destruct (Local [::] top top_found) as [before [Created Found]].
 rewrite Top in Found. inversion Found; subst before.
 exists top_before,top_after. split.
 - unfold create_initial_module in Created. rewrite module_found in Created. exact Created.
 - split; [exact External|]. rewrite States. apply SVM.Lemmas.find_add_eq. reflexivity.
Qed.
Lemma circuit_initial_child modules top previous external states instances path module_id ports body
 (instances_found:find_circuit_instances modules top=Some instances)
 (instance_found:SVM.find path instances=Some module_id)
 (module_found:find_module modules module_id=Some(FInmod module_id ports body))
 (nonroot:path<>[::])
 (ran:circuit_initial_map_with_memory modules top previous external=Some states) :
 exists env,
 statements_initial_map_with_memory modules body
 (match previous with Some maps=>SVM.find path maps|None=>None end) (ports_initial_map ports)=Some env /\ SVM.find path states=Some env.
Proof.
 destruct (circuit_initial_local _ _ _ _ _ _ instances_found ran) as [declared [top_before [top_after [actual [actual_ports [actual_body [Top [Module [External [States Local]]]]]]]]]].
 destruct (Local path module_id instance_found) as [env [Created Found]]. exists env. split.
 - unfold create_initial_module in Created. rewrite module_found in Created. exact Created.
 - rewrite States SVM.Lemmas.find_add_neq; [exact Found|]. intro Same. move/eqP:Same=>Same. exact(nonroot Same).
Qed.
