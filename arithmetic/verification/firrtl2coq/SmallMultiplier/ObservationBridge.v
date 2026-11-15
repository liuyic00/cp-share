From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalProgressTypes GlobalInitialLocal GlobalInitialLeaves GlobalInitialization GlobalConvergence.
Lemma global_rank_bound index (inside:Nat.lt index 2262) : Nat.le (global_rank_at index) 56.
Proof.
 have Checked: List.forallb (fun n=>Nat.leb(global_rank_at n)56)(List.seq 0 2262)=true by vm_compute;reflexivity.
 have Member:List.In index (List.seq 0 2262) by apply List.in_seq;lia.
 have Value := (proj1 (List.forallb_forall _ _) Checked) index Member.
 apply Nat.leb_le. exact Value.
Qed.
Definition multiplier_observe previous inputs :=
 match circuit_initial_map_with_memory generated_modules generated_top (Some previous) (formal_external_inputs inputs),
 circuit_iter_count_with_memory generated_modules generated_top Gtyp_connect_count with
 | Some initial,Some count=>circuit_formal_iterations generated_modules generated_top inputs count initial
 | _,_=>None end.
Lemma multiplier_iteration_count : circuit_iter_count_with_memory generated_modules generated_top Gtyp_connect_count=Some 2256%nat.
Proof. vm_compute. reflexivity. Qed.
Local Opaque circuit_initial_map_with_memory circuit_formal_iterations.
Theorem multiplier_observation_values v previous old inputs observed
 (sized:global_leaf_sizes v)
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v (formal_external_inputs inputs))
 (ran:multiplier_observe previous inputs=Some observed) :
 forall index,Nat.lt index 2262 -> global_value_at index observed=Some(global_target_at index v).
Proof.
 unfold multiplier_observe in ran. rewrite multiplier_iteration_count in ran.
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some previous) (formal_external_inputs inputs)) as [initial|] eqn:Initial; [|discriminate].
 have Ranked := multiplier_initial_ranked v previous old (formal_external_inputs inputs) initial old_found registers ports Initial.
 have Typed := multiplier_initial_types v (Some previous) (formal_external_inputs inputs) initial ports Initial.
 destruct (global_iterations_ranked v inputs 2256 initial observed 0 Ranked Typed sized ran) as [Final Types].
 intros index inside. apply Final; [exact inside|]. have Bound:=global_rank_bound index inside. cbn [Nat.add]. lia.
Qed.
