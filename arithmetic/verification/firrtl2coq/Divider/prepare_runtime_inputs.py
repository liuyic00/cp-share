from pathlib import Path
P=Path(__file__).resolve().parent
p=P/'RuntimeInputs.v';s=p.read_text().split('(* Generated external input projection facts. *)')[0]
s+='''\n(* Generated external input projection facts. *)\nLocal Transparent word_0 word_1 word_3 word_4 word_5 word_6 word_7 word_10 word_11 word_12.
Definition divider_ports := match generated_module_0 with FInmod _ ports _ => ports | _ => [::] end.
Lemma all_list_member (A:Type) (test:A->bool) items :
 forall item, all test items = true -> List.In item items -> test item = true.
Proof.
 induction items as [|head tail IH]; intros item checked member; [contradiction|].
 move/andP: checked => [H T]. destruct member as [same|member]; [subst; exact H|eapply IH; eassumption].
Qed.
Lemma runtime_external_port inputs id ground
 (member : List.In (Finput id (Gtyp ground)) divider_ports)
 (defined : formal_external_inputs_defined generated_modules generated_top inputs = true) :
 VM.find id (formal_external_inputs inputs) = Some (Gval ground (external_bits inputs id)) /\\
 size (external_bits inputs id) = sizeof_fgtyp ground.
Proof.
 have ports : all (external_port_defined (formal_external_inputs inputs)) divider_ports = true by exact defined.
 have port := all_list_member _ _ _ _ ports member.
 destruct (ground_external_port_defined _ _ _ port) as [bits [Found Sized]].
 unfold external_bits. rewrite Found. split; [reflexivity|exact Sized].
Qed.
'''
ids=[0,1,3,4,5,6,7,10,11,12];ws={x:64 if x in [4,5,6] else 1 for x in ids}
for id in ids:
 gt='Fclock' if id==0 else f'(Fuint {ws[id]})'
 s+=f'''Lemma runtime_port_{id} inputs
 (defined : formal_external_inputs_defined generated_modules generated_top inputs = true) :
 VM.find {id} (formal_external_inputs inputs) = Some (Gval {gt} (external_bits inputs {id})) /\\ size (external_bits inputs {id}) = {ws[id]}%nat.
Proof. apply runtime_external_port; [vm_compute; tauto|exact defined]. Qed.
Lemma runtime_leaf_{id} state inputs ghost
 (defined : formal_external_inputs_defined generated_modules generated_top inputs = true) :
 VM.find {id} (formal_external_inputs inputs) = Some (Gval {gt} (runtime_leaves state inputs ghost {id})).
Proof.
 destruct (runtime_port_{id} inputs defined) as [Found Sized].
 change (VM.find {id} (formal_external_inputs inputs) = Some (Gval {gt} ({('external_bits inputs '+str(id)) if id==0 else ('encode '+str(ws[id])+' (to_Zpos (external_bits inputs '+str(id)+'))')}))).
'''
 s+= (' exact Found.\n' if id==0 else ' rewrite encode_decode_bits; [exact Found|exact Sized].\n')+'Qed.\n'
s+='''Lemma runtime_leaf_sizes state inputs ghost
 (defined : formal_external_inputs_defined generated_modules generated_top inputs = true) :
 divider_leaves_sized (runtime_leaves state inputs ghost).
Proof.
 unfold divider_leaves_sized, runtime_leaves, with_clock, encoded_leaves.
 repeat split; try apply encode_size. exact (proj2 (runtime_port_0 inputs defined)).
Qed.
Lemma runtime_port_values state inputs ghost
 (defined : formal_external_inputs_defined generated_modules generated_top inputs = true) :
 divider_input_values (runtime_leaves state inputs ghost) (formal_external_inputs inputs).
Proof.
 intros id inside.
'''
for id in ids:
 gt='Fclock' if id==0 else f'(Fuint {ws[id]})'
 s+=f''' destruct inside as [same|inside].
 - subst id. rewrite target_{id}_value.
   change (VM.find {id} (formal_external_inputs inputs) = Some (Gval {gt} (runtime_leaves state inputs ghost {id}))).
   exact (runtime_leaf_{id} state inputs ghost defined).
'''
s+=' contradiction.\nQed.\nPrint Assumptions runtime_port_values.\n'
p.write_text(s)
