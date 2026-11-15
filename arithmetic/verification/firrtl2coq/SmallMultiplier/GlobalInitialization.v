From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model GlobalStable GlobalInstances GlobalProgressTypes GlobalInitialLocal GlobalInitialTypes.
Local Open Scope N_scope.
From SmallMultiplier Require Import GlobalInitialAll0 GlobalInitialAll1 GlobalInitialAll2 GlobalInitialAll3 GlobalInitialAll4 GlobalInitialAll5 GlobalInitialAll6 GlobalInitialAll7 GlobalInitialAll8 GlobalInitialAll9 GlobalInitialAll10 GlobalInitialAll11.
Theorem multiplier_initial_types v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 global_port_types states.
Proof. intros index inside.
 destruct (lt_dec index 200) as [Range|Range0].
 - apply (global_initial_type_chunk_0 v previous external states ports ran index);lia.
 destruct (lt_dec index 400) as [Range|Range1].
 - apply (global_initial_type_chunk_1 v previous external states ports ran index);lia.
 destruct (lt_dec index 600) as [Range|Range2].
 - apply (global_initial_type_chunk_2 v previous external states ports ran index);lia.
 destruct (lt_dec index 800) as [Range|Range3].
 - apply (global_initial_type_chunk_3 v previous external states ports ran index);lia.
 destruct (lt_dec index 1000) as [Range|Range4].
 - apply (global_initial_type_chunk_4 v previous external states ports ran index);lia.
 destruct (lt_dec index 1200) as [Range|Range5].
 - apply (global_initial_type_chunk_5 v previous external states ports ran index);lia.
 destruct (lt_dec index 1400) as [Range|Range6].
 - apply (global_initial_type_chunk_6 v previous external states ports ran index);lia.
 destruct (lt_dec index 1600) as [Range|Range7].
 - apply (global_initial_type_chunk_7 v previous external states ports ran index);lia.
 destruct (lt_dec index 1800) as [Range|Range8].
 - apply (global_initial_type_chunk_8 v previous external states ports ran index);lia.
 destruct (lt_dec index 2000) as [Range|Range9].
 - apply (global_initial_type_chunk_9 v previous external states ports ran index);lia.
 destruct (lt_dec index 2200) as [Range|Range10].
 - apply (global_initial_type_chunk_10 v previous external states ports ran index);lia.
 apply (global_initial_type_chunk_11 v previous external states ports ran index);lia.
Qed.
