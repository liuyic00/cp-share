From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalInstances GlobalInitialLocal GlobalProgressTypes PipelineInvariant.
Local Open Scope N_scope.
Lemma ground_external_port_defined external id ground
 (defined:external_port_defined external (@Finput VarOrder.T id (Gtyp ground))=true) :
 exists bits,VM.find id external=Some(Gval ground bits) /\ size bits=sizeof_fgtyp ground.
Proof.
 cbn [external_port_defined type_has_input] in defined.
 destruct (VM.find id external) as [value|] eqn:Found; [|discriminate].
 destruct value; cbn [known_input_value type_has_input] in defined; try discriminate.
 move/andP:defined => [/eqP Same /eqP Sized]. subst f.
 exists b;split;[reflexivity|exact Sized].
Qed.
Definition external_bits (inputs:formal_inputs) (id:VarOrder.T) :=
 match VM.find id (formal_external_inputs inputs) with Some(Gval _ b)=>b|_=>[::]end.
Lemma all_list_member (A:Type) (test:A->bool) items :
 forall item,all test items=true -> List.In item items -> test item=true.
Proof.
 induction items as [|head tail IH];intros item checked member;[contradiction|].
 move/andP:checked => [H T]. destruct member as [same|member];[subst;exact H|eapply IH;eassumption].
Qed.
Lemma runtime_external_port inputs id ground
 (member:List.In (Finput id (Gtyp ground)) (multiplier_ports 3))
 (defined:formal_external_inputs_defined generated_modules generated_top inputs=true) :
 VM.find id (formal_external_inputs inputs)=Some(Gval ground(external_bits inputs id)) /\ size(external_bits inputs id)=sizeof_fgtyp ground.
Proof.
 have Ports:all (external_port_defined(formal_external_inputs inputs)) (multiplier_ports 3)=true by exact defined.
 have Port:=all_list_member _ _ _ _ Ports member.
 destruct (ground_external_port_defined _ _ _ Port) as [bits [Found Sized]].
 unfold external_bits. rewrite Found. split;[reflexivity|exact Sized].
Qed.
Lemma runtime_port_0 inputs (defined:formal_external_inputs_defined generated_modules generated_top inputs=true) :
 VM.find 0 (formal_external_inputs inputs)=Some(Gval Fclock(external_bits inputs 0)) /\ size(external_bits inputs 0)=1%nat.
Proof. apply runtime_external_port;[vm_compute;tauto|exact defined]. Qed.
Lemma runtime_port_1 inputs (defined:formal_external_inputs_defined generated_modules generated_top inputs=true) :
 VM.find 1 (formal_external_inputs inputs)=Some(Gval (Fuint 1)(external_bits inputs 1)) /\ size(external_bits inputs 1)=1%nat.
Proof. apply runtime_external_port;[vm_compute;tauto|exact defined]. Qed.
Lemma runtime_port_2 inputs (defined:formal_external_inputs_defined generated_modules generated_top inputs=true) :
 VM.find 2 (formal_external_inputs inputs)=Some(Gval (Fuint 8)(external_bits inputs 2)) /\ size(external_bits inputs 2)=8%nat.
Proof. apply runtime_external_port;[vm_compute;tauto|exact defined]. Qed.
Lemma runtime_port_3 inputs (defined:formal_external_inputs_defined generated_modules generated_top inputs=true) :
 VM.find 3 (formal_external_inputs inputs)=Some(Gval (Fuint 8)(external_bits inputs 3)) /\ size(external_bits inputs 3)=8%nat.
Proof. apply runtime_external_port;[vm_compute;tauto|exact defined]. Qed.
Lemma runtime_port_4 inputs (defined:formal_external_inputs_defined generated_modules generated_top inputs=true) :
 VM.find 4 (formal_external_inputs inputs)=Some(Gval (Fuint 1)(external_bits inputs 4)) /\ size(external_bits inputs 4)=1%nat.
Proof. apply runtime_external_port;[vm_compute;tauto|exact defined]. Qed.
Lemma runtime_port_5 inputs (defined:formal_external_inputs_defined generated_modules generated_top inputs=true) :
 VM.find 5 (formal_external_inputs inputs)=Some(Gval (Fuint 1)(external_bits inputs 5)) /\ size(external_bits inputs 5)=1%nat.
Proof. apply runtime_external_port;[vm_compute;tauto|exact defined]. Qed.
Definition runtime_leaves (v:global_leaves) inputs : global_leaves := fun index=>match N.of_nat index with
| 0=>external_bits inputs 0
| 1=>external_bits inputs 1
| 2=>external_bits inputs 2
| 53=>external_bits inputs 3
| 56=>external_bits inputs 4
| 61=>external_bits inputs 5
| _=>v index end.
Lemma runtime_input_values v inputs (defined:formal_external_inputs_defined generated_modules generated_top inputs=true) :
 multiplier_input_values (runtime_leaves v inputs) (formal_external_inputs inputs).
Proof. repeat split.
 exact(proj1(runtime_port_0 inputs defined)).
 exact(proj1(runtime_port_1 inputs defined)).
 exact(proj1(runtime_port_2 inputs defined)).
 exact(proj1(runtime_port_3 inputs defined)).
 exact(proj1(runtime_port_4 inputs defined)).
 exact(proj1(runtime_port_5 inputs defined)).
Qed.
Lemma runtime_leaf_sizes v inputs (sized:global_leaf_sizes v) (defined:formal_external_inputs_defined generated_modules generated_top inputs=true) :
 global_leaf_sizes(runtime_leaves v inputs).
Proof. intros index inside.
 have Member:List.In index (List.seq 0 62) by apply List.in_seq; move/ltP:inside;lia.
 change (List.In index [::0%nat;1%nat;2%nat;3%nat;4%nat;5%nat;6%nat;7%nat;8%nat;9%nat;10%nat;11%nat;12%nat;13%nat;14%nat;15%nat;16%nat;17%nat;18%nat;19%nat;20%nat;21%nat;22%nat;23%nat;24%nat;25%nat;26%nat;27%nat;28%nat;29%nat;30%nat;31%nat;32%nat;33%nat;34%nat;35%nat;36%nat;37%nat;38%nat;39%nat;40%nat;41%nat;42%nat;43%nat;44%nat;45%nat;46%nat;47%nat;48%nat;49%nat;50%nat;51%nat;52%nat;53%nat;54%nat;55%nat;56%nat;57%nat;58%nat;59%nat;60%nat;61%nat]) in Member.
 destruct Member as [same|Member].
 - subst index. exact(proj2(runtime_port_0 inputs defined)).
 destruct Member as [same|Member].
 - subst index. exact(proj2(runtime_port_1 inputs defined)).
 destruct Member as [same|Member].
 - subst index. exact(proj2(runtime_port_2 inputs defined)).
 destruct Member as [same|Member].
 - subst index. exact(sized 3%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 4%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 5%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 6%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 7%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 8%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 9%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 10%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 11%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 12%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 13%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 14%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 15%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 16%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 17%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 18%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 19%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 20%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 21%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 22%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 23%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 24%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 25%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 26%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 27%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 28%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 29%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 30%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 31%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 32%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 33%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 34%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 35%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 36%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 37%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 38%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 39%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 40%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 41%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 42%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 43%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 44%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 45%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 46%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 47%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 48%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 49%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 50%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 51%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 52%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(proj2(runtime_port_3 inputs defined)).
 destruct Member as [same|Member].
 - subst index. exact(sized 54%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 55%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(proj2(runtime_port_4 inputs defined)).
 destruct Member as [same|Member].
 - subst index. exact(sized 57%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 58%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 59%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 60%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(proj2(runtime_port_5 inputs defined)).
 contradiction.
Qed.
Lemma runtime_register_values v inputs env (registers:multiplier_register_values v env) :
 multiplier_register_values(runtime_leaves v inputs) env.
Proof. intros index inside.
 destruct inside as [same|inside].
 - subst index. exact(registers 3%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 4%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 5%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 6%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 7%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 8%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 9%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 10%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 11%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 12%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 13%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 14%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 15%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 16%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 17%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 18%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 19%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 20%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 21%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 22%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 23%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 24%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 25%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 26%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 27%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 28%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 29%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 30%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 31%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 32%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 33%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 34%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 35%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 36%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 37%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 38%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 39%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 40%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 41%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 42%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 43%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 44%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 45%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 46%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 47%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 48%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 49%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 50%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 51%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 52%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 54%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 55%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 57%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 58%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 59%nat (ltac:(unfold List.In;tauto))).
 destruct inside as [same|inside].
 - subst index. exact(registers 60%nat (ltac:(unfold List.In;tauto))).
 contradiction.
Qed.
Lemma runtime_invariant v inputs (invariant:pipeline_invariant v) : pipeline_invariant(runtime_leaves v inputs).
Proof. exact invariant. Qed.
