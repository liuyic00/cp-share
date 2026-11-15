From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
From ArithmeticCommon Require Import BitvectorFacts.
From Divider Require Import Model Stable Representation Frames SingleModule Initialization RuntimeRepresentation Bridge.
Local Open Scope N_scope.
Lemma encode_decode_bits width bits (sized : size bits = width) :
 encode width (to_Zpos bits) = bits.
Proof. unfold encode. rewrite (unsigned_normalized width bits sized) -sized. apply from_Zpos_to_Zpos. Qed.
Lemma ground_external_port_defined external id ground
 (defined : external_port_defined external (@Finput VarOrder.T id (Gtyp ground)) = true) :
 exists bits, VM.find id external = Some (Gval ground bits) /\ size bits = sizeof_fgtyp ground.
Proof.
 cbn [external_port_defined type_has_input] in defined.
 destruct (VM.find id external) as [value|] eqn:Found; try discriminate.
 destruct value; cbn [known_input_value type_has_input] in defined; try discriminate.
 move/andP: defined => [/eqP Same /eqP Sized]. subst f.
 exists b; split; [reflexivity|exact Sized].
Qed.
Definition external_bits (inputs : formal_inputs) (id : VarOrder.T) : seq bool :=
 match VM.find id (formal_external_inputs inputs) with Some (Gval _ bits) => bits | _ => [::] end.
Definition runtime_inputs inputs : Reference.Inputs := Reference.mkInputs
 (to_Zpos (external_bits inputs 1)) (to_Zpos (external_bits inputs 3))
 (to_Zpos (external_bits inputs 4)) (to_Zpos (external_bits inputs 5))
 (to_Zpos (external_bits inputs 6)) (to_Zpos (external_bits inputs 7))
 (to_Zpos (external_bits inputs 10)) (to_Zpos (external_bits inputs 11))
 (to_Zpos (external_bits inputs 12)).
Definition runtime_leaves state inputs ghost :=
 with_clock (encoded_leaves state (runtime_inputs inputs) ghost) (external_bits inputs 0).



(* Generated external input projection facts. *)
Local Transparent word_0 word_1 word_3 word_4 word_5 word_6 word_7 word_10 word_11 word_12.
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
 VM.find id (formal_external_inputs inputs) = Some (Gval ground (external_bits inputs id)) /\
 size (external_bits inputs id) = sizeof_fgtyp ground.
Proof.
 have ports : all (external_port_defined (formal_external_inputs inputs)) divider_ports = true by exact defined.
 have port := all_list_member _ _ _ _ ports member.
 destruct (ground_external_port_defined _ _ _ port) as [bits [Found Sized]].
 unfold external_bits. rewrite Found. split; [reflexivity|exact Sized].
Qed.
Lemma runtime_port_0 inputs
 (defined : formal_external_inputs_defined generated_modules generated_top inputs = true) :
 VM.find 0 (formal_external_inputs inputs) = Some (Gval Fclock (external_bits inputs 0)) /\ size (external_bits inputs 0) = 1%nat.
Proof. apply runtime_external_port; [vm_compute; tauto|exact defined]. Qed.
Lemma runtime_leaf_0 state inputs ghost
 (defined : formal_external_inputs_defined generated_modules generated_top inputs = true) :
 VM.find 0 (formal_external_inputs inputs) = Some (Gval Fclock (runtime_leaves state inputs ghost 0)).
Proof.
 destruct (runtime_port_0 inputs defined) as [Found Sized].
 change (VM.find 0 (formal_external_inputs inputs) = Some (Gval Fclock (external_bits inputs 0))).
 exact Found.
Qed.
Lemma runtime_port_1 inputs
 (defined : formal_external_inputs_defined generated_modules generated_top inputs = true) :
 VM.find 1 (formal_external_inputs inputs) = Some (Gval (Fuint 1) (external_bits inputs 1)) /\ size (external_bits inputs 1) = 1%nat.
Proof. apply runtime_external_port; [vm_compute; tauto|exact defined]. Qed.
Lemma runtime_leaf_1 state inputs ghost
 (defined : formal_external_inputs_defined generated_modules generated_top inputs = true) :
 VM.find 1 (formal_external_inputs inputs) = Some (Gval (Fuint 1) (runtime_leaves state inputs ghost 1)).
Proof.
 destruct (runtime_port_1 inputs defined) as [Found Sized].
 change (VM.find 1 (formal_external_inputs inputs) = Some (Gval (Fuint 1) (encode 1 (to_Zpos (external_bits inputs 1))))).
 rewrite encode_decode_bits; [exact Found|exact Sized].
Qed.
Lemma runtime_port_3 inputs
 (defined : formal_external_inputs_defined generated_modules generated_top inputs = true) :
 VM.find 3 (formal_external_inputs inputs) = Some (Gval (Fuint 1) (external_bits inputs 3)) /\ size (external_bits inputs 3) = 1%nat.
Proof. apply runtime_external_port; [vm_compute; tauto|exact defined]. Qed.
Lemma runtime_leaf_3 state inputs ghost
 (defined : formal_external_inputs_defined generated_modules generated_top inputs = true) :
 VM.find 3 (formal_external_inputs inputs) = Some (Gval (Fuint 1) (runtime_leaves state inputs ghost 3)).
Proof.
 destruct (runtime_port_3 inputs defined) as [Found Sized].
 change (VM.find 3 (formal_external_inputs inputs) = Some (Gval (Fuint 1) (encode 1 (to_Zpos (external_bits inputs 3))))).
 rewrite encode_decode_bits; [exact Found|exact Sized].
Qed.
Lemma runtime_port_4 inputs
 (defined : formal_external_inputs_defined generated_modules generated_top inputs = true) :
 VM.find 4 (formal_external_inputs inputs) = Some (Gval (Fuint 64) (external_bits inputs 4)) /\ size (external_bits inputs 4) = 64%nat.
Proof. apply runtime_external_port; [vm_compute; tauto|exact defined]. Qed.
Lemma runtime_leaf_4 state inputs ghost
 (defined : formal_external_inputs_defined generated_modules generated_top inputs = true) :
 VM.find 4 (formal_external_inputs inputs) = Some (Gval (Fuint 64) (runtime_leaves state inputs ghost 4)).
Proof.
 destruct (runtime_port_4 inputs defined) as [Found Sized].
 change (VM.find 4 (formal_external_inputs inputs) = Some (Gval (Fuint 64) (encode 64 (to_Zpos (external_bits inputs 4))))).
 rewrite encode_decode_bits; [exact Found|exact Sized].
Qed.
Lemma runtime_port_5 inputs
 (defined : formal_external_inputs_defined generated_modules generated_top inputs = true) :
 VM.find 5 (formal_external_inputs inputs) = Some (Gval (Fuint 64) (external_bits inputs 5)) /\ size (external_bits inputs 5) = 64%nat.
Proof. apply runtime_external_port; [vm_compute; tauto|exact defined]. Qed.
Lemma runtime_leaf_5 state inputs ghost
 (defined : formal_external_inputs_defined generated_modules generated_top inputs = true) :
 VM.find 5 (formal_external_inputs inputs) = Some (Gval (Fuint 64) (runtime_leaves state inputs ghost 5)).
Proof.
 destruct (runtime_port_5 inputs defined) as [Found Sized].
 change (VM.find 5 (formal_external_inputs inputs) = Some (Gval (Fuint 64) (encode 64 (to_Zpos (external_bits inputs 5))))).
 rewrite encode_decode_bits; [exact Found|exact Sized].
Qed.
Lemma runtime_port_6 inputs
 (defined : formal_external_inputs_defined generated_modules generated_top inputs = true) :
 VM.find 6 (formal_external_inputs inputs) = Some (Gval (Fuint 64) (external_bits inputs 6)) /\ size (external_bits inputs 6) = 64%nat.
Proof. apply runtime_external_port; [vm_compute; tauto|exact defined]. Qed.
Lemma runtime_leaf_6 state inputs ghost
 (defined : formal_external_inputs_defined generated_modules generated_top inputs = true) :
 VM.find 6 (formal_external_inputs inputs) = Some (Gval (Fuint 64) (runtime_leaves state inputs ghost 6)).
Proof.
 destruct (runtime_port_6 inputs defined) as [Found Sized].
 change (VM.find 6 (formal_external_inputs inputs) = Some (Gval (Fuint 64) (encode 64 (to_Zpos (external_bits inputs 6))))).
 rewrite encode_decode_bits; [exact Found|exact Sized].
Qed.
Lemma runtime_port_7 inputs
 (defined : formal_external_inputs_defined generated_modules generated_top inputs = true) :
 VM.find 7 (formal_external_inputs inputs) = Some (Gval (Fuint 1) (external_bits inputs 7)) /\ size (external_bits inputs 7) = 1%nat.
Proof. apply runtime_external_port; [vm_compute; tauto|exact defined]. Qed.
Lemma runtime_leaf_7 state inputs ghost
 (defined : formal_external_inputs_defined generated_modules generated_top inputs = true) :
 VM.find 7 (formal_external_inputs inputs) = Some (Gval (Fuint 1) (runtime_leaves state inputs ghost 7)).
Proof.
 destruct (runtime_port_7 inputs defined) as [Found Sized].
 change (VM.find 7 (formal_external_inputs inputs) = Some (Gval (Fuint 1) (encode 1 (to_Zpos (external_bits inputs 7))))).
 rewrite encode_decode_bits; [exact Found|exact Sized].
Qed.
Lemma runtime_port_10 inputs
 (defined : formal_external_inputs_defined generated_modules generated_top inputs = true) :
 VM.find 10 (formal_external_inputs inputs) = Some (Gval (Fuint 1) (external_bits inputs 10)) /\ size (external_bits inputs 10) = 1%nat.
Proof. apply runtime_external_port; [vm_compute; tauto|exact defined]. Qed.
Lemma runtime_leaf_10 state inputs ghost
 (defined : formal_external_inputs_defined generated_modules generated_top inputs = true) :
 VM.find 10 (formal_external_inputs inputs) = Some (Gval (Fuint 1) (runtime_leaves state inputs ghost 10)).
Proof.
 destruct (runtime_port_10 inputs defined) as [Found Sized].
 change (VM.find 10 (formal_external_inputs inputs) = Some (Gval (Fuint 1) (encode 1 (to_Zpos (external_bits inputs 10))))).
 rewrite encode_decode_bits; [exact Found|exact Sized].
Qed.
Lemma runtime_port_11 inputs
 (defined : formal_external_inputs_defined generated_modules generated_top inputs = true) :
 VM.find 11 (formal_external_inputs inputs) = Some (Gval (Fuint 1) (external_bits inputs 11)) /\ size (external_bits inputs 11) = 1%nat.
Proof. apply runtime_external_port; [vm_compute; tauto|exact defined]. Qed.
Lemma runtime_leaf_11 state inputs ghost
 (defined : formal_external_inputs_defined generated_modules generated_top inputs = true) :
 VM.find 11 (formal_external_inputs inputs) = Some (Gval (Fuint 1) (runtime_leaves state inputs ghost 11)).
Proof.
 destruct (runtime_port_11 inputs defined) as [Found Sized].
 change (VM.find 11 (formal_external_inputs inputs) = Some (Gval (Fuint 1) (encode 1 (to_Zpos (external_bits inputs 11))))).
 rewrite encode_decode_bits; [exact Found|exact Sized].
Qed.
Lemma runtime_port_12 inputs
 (defined : formal_external_inputs_defined generated_modules generated_top inputs = true) :
 VM.find 12 (formal_external_inputs inputs) = Some (Gval (Fuint 1) (external_bits inputs 12)) /\ size (external_bits inputs 12) = 1%nat.
Proof. apply runtime_external_port; [vm_compute; tauto|exact defined]. Qed.
Lemma runtime_leaf_12 state inputs ghost
 (defined : formal_external_inputs_defined generated_modules generated_top inputs = true) :
 VM.find 12 (formal_external_inputs inputs) = Some (Gval (Fuint 1) (runtime_leaves state inputs ghost 12)).
Proof.
 destruct (runtime_port_12 inputs defined) as [Found Sized].
 change (VM.find 12 (formal_external_inputs inputs) = Some (Gval (Fuint 1) (encode 1 (to_Zpos (external_bits inputs 12))))).
 rewrite encode_decode_bits; [exact Found|exact Sized].
Qed.
Lemma runtime_leaf_sizes state inputs ghost
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
 destruct inside as [same|inside].
 - subst id. rewrite target_0_value.
   change (VM.find 0 (formal_external_inputs inputs) = Some (Gval Fclock (runtime_leaves state inputs ghost 0))).
   exact (runtime_leaf_0 state inputs ghost defined).
 destruct inside as [same|inside].
 - subst id. rewrite target_1_value.
   change (VM.find 1 (formal_external_inputs inputs) = Some (Gval (Fuint 1) (runtime_leaves state inputs ghost 1))).
   exact (runtime_leaf_1 state inputs ghost defined).
 destruct inside as [same|inside].
 - subst id. rewrite target_3_value.
   change (VM.find 3 (formal_external_inputs inputs) = Some (Gval (Fuint 1) (runtime_leaves state inputs ghost 3))).
   exact (runtime_leaf_3 state inputs ghost defined).
 destruct inside as [same|inside].
 - subst id. rewrite target_4_value.
   change (VM.find 4 (formal_external_inputs inputs) = Some (Gval (Fuint 64) (runtime_leaves state inputs ghost 4))).
   exact (runtime_leaf_4 state inputs ghost defined).
 destruct inside as [same|inside].
 - subst id. rewrite target_5_value.
   change (VM.find 5 (formal_external_inputs inputs) = Some (Gval (Fuint 64) (runtime_leaves state inputs ghost 5))).
   exact (runtime_leaf_5 state inputs ghost defined).
 destruct inside as [same|inside].
 - subst id. rewrite target_6_value.
   change (VM.find 6 (formal_external_inputs inputs) = Some (Gval (Fuint 64) (runtime_leaves state inputs ghost 6))).
   exact (runtime_leaf_6 state inputs ghost defined).
 destruct inside as [same|inside].
 - subst id. rewrite target_7_value.
   change (VM.find 7 (formal_external_inputs inputs) = Some (Gval (Fuint 1) (runtime_leaves state inputs ghost 7))).
   exact (runtime_leaf_7 state inputs ghost defined).
 destruct inside as [same|inside].
 - subst id. rewrite target_10_value.
   change (VM.find 10 (formal_external_inputs inputs) = Some (Gval (Fuint 1) (runtime_leaves state inputs ghost 10))).
   exact (runtime_leaf_10 state inputs ghost defined).
 destruct inside as [same|inside].
 - subst id. rewrite target_11_value.
   change (VM.find 11 (formal_external_inputs inputs) = Some (Gval (Fuint 1) (runtime_leaves state inputs ghost 11))).
   exact (runtime_leaf_11 state inputs ghost defined).
 destruct inside as [same|inside].
 - subst id. rewrite target_12_value.
   change (VM.find 12 (formal_external_inputs inputs) = Some (Gval (Fuint 1) (runtime_leaves state inputs ghost 12))).
   exact (runtime_leaf_12 state inputs ghost defined).
 contradiction.
Qed.
Print Assumptions runtime_port_values.
