From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalProgressTypes GlobalFieldSteps GlobalScalarSteps GlobalProgress.
Local Open Scope N_scope.
From SmallMultiplier Require Import GlobalConvergence0 GlobalConvergence1 GlobalConvergence2 GlobalConvergence3 GlobalConvergence4 GlobalConvergence5 GlobalConvergence6 GlobalConvergence7 GlobalConvergence8 GlobalConvergence9 GlobalConvergence10 GlobalConvergence11.
Lemma finite_forall (P:nat->Prop) start count index
 (checked:List.Forall P (List.seq start count))
 (inside:Nat.le start index /\ Nat.lt index (Nat.add start count)) : P index.
Proof. apply (proj1 (List.Forall_forall P _) checked). apply List.in_seq. exact inside. Qed.
Lemma global_rank_step invalid snapshot final v level (prior:global_ranked v level snapshot) (sizes:global_leaf_sizes v)
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 global_ranked v (S level) final.
Proof. intros index inside.
 destruct (lt_dec index 200) as [Range|Range0].
 - exact (finite_forall (fun n => (global_rank_at n <= S level)%coq_nat -> global_value_at n final = Some (global_target_at n v)) 0 200 index (global_rank_chunk_0 invalid snapshot final v level prior sizes types ran) (ltac:(lia))).
 destruct (lt_dec index 400) as [Range|Range1].
 - exact (finite_forall (fun n => (global_rank_at n <= S level)%coq_nat -> global_value_at n final = Some (global_target_at n v)) 200 200 index (global_rank_chunk_1 invalid snapshot final v level prior sizes types ran) (ltac:(lia))).
 destruct (lt_dec index 600) as [Range|Range2].
 - exact (finite_forall (fun n => (global_rank_at n <= S level)%coq_nat -> global_value_at n final = Some (global_target_at n v)) 400 200 index (global_rank_chunk_2 invalid snapshot final v level prior sizes types ran) (ltac:(lia))).
 destruct (lt_dec index 800) as [Range|Range3].
 - exact (finite_forall (fun n => (global_rank_at n <= S level)%coq_nat -> global_value_at n final = Some (global_target_at n v)) 600 200 index (global_rank_chunk_3 invalid snapshot final v level prior sizes types ran) (ltac:(lia))).
 destruct (lt_dec index 1000) as [Range|Range4].
 - exact (finite_forall (fun n => (global_rank_at n <= S level)%coq_nat -> global_value_at n final = Some (global_target_at n v)) 800 200 index (global_rank_chunk_4 invalid snapshot final v level prior sizes types ran) (ltac:(lia))).
 destruct (lt_dec index 1200) as [Range|Range5].
 - exact (finite_forall (fun n => (global_rank_at n <= S level)%coq_nat -> global_value_at n final = Some (global_target_at n v)) 1000 200 index (global_rank_chunk_5 invalid snapshot final v level prior sizes types ran) (ltac:(lia))).
 destruct (lt_dec index 1400) as [Range|Range6].
 - exact (finite_forall (fun n => (global_rank_at n <= S level)%coq_nat -> global_value_at n final = Some (global_target_at n v)) 1200 200 index (global_rank_chunk_6 invalid snapshot final v level prior sizes types ran) (ltac:(lia))).
 destruct (lt_dec index 1600) as [Range|Range7].
 - exact (finite_forall (fun n => (global_rank_at n <= S level)%coq_nat -> global_value_at n final = Some (global_target_at n v)) 1400 200 index (global_rank_chunk_7 invalid snapshot final v level prior sizes types ran) (ltac:(lia))).
 destruct (lt_dec index 1800) as [Range|Range8].
 - exact (finite_forall (fun n => (global_rank_at n <= S level)%coq_nat -> global_value_at n final = Some (global_target_at n v)) 1600 200 index (global_rank_chunk_8 invalid snapshot final v level prior sizes types ran) (ltac:(lia))).
 destruct (lt_dec index 2000) as [Range|Range9].
 - exact (finite_forall (fun n => (global_rank_at n <= S level)%coq_nat -> global_value_at n final = Some (global_target_at n v)) 1800 200 index (global_rank_chunk_9 invalid snapshot final v level prior sizes types ran) (ltac:(lia))).
 destruct (lt_dec index 2200) as [Range|Range10].
 - exact (finite_forall (fun n => (global_rank_at n <= S level)%coq_nat -> global_value_at n final = Some (global_target_at n v)) 2000 200 index (global_rank_chunk_10 invalid snapshot final v level prior sizes types ran) (ltac:(lia))).
 exact (finite_forall (fun n => (global_rank_at n <= S level)%coq_nat -> global_value_at n final = Some (global_target_at n v)) 2200 62 index (global_rank_chunk_11 invalid snapshot final v level prior sizes types ran) (ltac:(lia))).
Qed.
Lemma global_type_step invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 global_port_types final.
Proof. intros index inside.
 destruct (lt_dec index 200) as [Range|Range0].
 - exact (finite_forall (fun n => global_port_at n=true -> option_map type_of_val (global_value_at n final)=Some(Gtyp(global_type_at n))) 0 200 index (global_type_chunk_0 invalid snapshot final types ran) (ltac:(lia))).
 destruct (lt_dec index 400) as [Range|Range1].
 - exact (finite_forall (fun n => global_port_at n=true -> option_map type_of_val (global_value_at n final)=Some(Gtyp(global_type_at n))) 200 200 index (global_type_chunk_1 invalid snapshot final types ran) (ltac:(lia))).
 destruct (lt_dec index 600) as [Range|Range2].
 - exact (finite_forall (fun n => global_port_at n=true -> option_map type_of_val (global_value_at n final)=Some(Gtyp(global_type_at n))) 400 200 index (global_type_chunk_2 invalid snapshot final types ran) (ltac:(lia))).
 destruct (lt_dec index 800) as [Range|Range3].
 - exact (finite_forall (fun n => global_port_at n=true -> option_map type_of_val (global_value_at n final)=Some(Gtyp(global_type_at n))) 600 200 index (global_type_chunk_3 invalid snapshot final types ran) (ltac:(lia))).
 destruct (lt_dec index 1000) as [Range|Range4].
 - exact (finite_forall (fun n => global_port_at n=true -> option_map type_of_val (global_value_at n final)=Some(Gtyp(global_type_at n))) 800 200 index (global_type_chunk_4 invalid snapshot final types ran) (ltac:(lia))).
 destruct (lt_dec index 1200) as [Range|Range5].
 - exact (finite_forall (fun n => global_port_at n=true -> option_map type_of_val (global_value_at n final)=Some(Gtyp(global_type_at n))) 1000 200 index (global_type_chunk_5 invalid snapshot final types ran) (ltac:(lia))).
 destruct (lt_dec index 1400) as [Range|Range6].
 - exact (finite_forall (fun n => global_port_at n=true -> option_map type_of_val (global_value_at n final)=Some(Gtyp(global_type_at n))) 1200 200 index (global_type_chunk_6 invalid snapshot final types ran) (ltac:(lia))).
 destruct (lt_dec index 1600) as [Range|Range7].
 - exact (finite_forall (fun n => global_port_at n=true -> option_map type_of_val (global_value_at n final)=Some(Gtyp(global_type_at n))) 1400 200 index (global_type_chunk_7 invalid snapshot final types ran) (ltac:(lia))).
 destruct (lt_dec index 1800) as [Range|Range8].
 - exact (finite_forall (fun n => global_port_at n=true -> option_map type_of_val (global_value_at n final)=Some(Gtyp(global_type_at n))) 1600 200 index (global_type_chunk_8 invalid snapshot final types ran) (ltac:(lia))).
 destruct (lt_dec index 2000) as [Range|Range9].
 - exact (finite_forall (fun n => global_port_at n=true -> option_map type_of_val (global_value_at n final)=Some(Gtyp(global_type_at n))) 1800 200 index (global_type_chunk_9 invalid snapshot final types ran) (ltac:(lia))).
 destruct (lt_dec index 2200) as [Range|Range10].
 - exact (finite_forall (fun n => global_port_at n=true -> option_map type_of_val (global_value_at n final)=Some(Gtyp(global_type_at n))) 2000 200 index (global_type_chunk_10 invalid snapshot final types ran) (ltac:(lia))).
 exact (finite_forall (fun n => global_port_at n=true -> option_map type_of_val (global_value_at n final)=Some(Gtyp(global_type_at n))) 2200 62 index (global_type_chunk_11 invalid snapshot final types ran) (ltac:(lia))).
Qed.
Local Opaque circuit_value_iter_with_memory_policy.
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
