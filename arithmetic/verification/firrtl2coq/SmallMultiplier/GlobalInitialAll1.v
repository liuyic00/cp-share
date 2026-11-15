From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model GlobalStable GlobalInstances GlobalProgressTypes GlobalInitialLocal GlobalInitialTypes.
Local Open Scope N_scope.
Lemma global_initial_type_chunk_1 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 forall index,(Nat.le 200 index /\ Nat.lt index 400) ->
 global_port_at index=true -> option_map type_of_val(global_value_at index states)=Some(Gtyp(global_type_at index)).
Proof.
 intros index Range.
 remember (Nat.sub index 200) as offset eqn:Offset.
 have Index:index=Nat.add 200 offset by lia.
 have Bound:(offset < 200)%coq_nat by lia.
 rewrite Index.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_278 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_281 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_289 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_293 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_296 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_299 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_307 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_311 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_314 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_317 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_320 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_331 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_335 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_338 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_341 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_344 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_355 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_359 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_362 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_365 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_368 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_370 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_373 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_375 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_378 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_380 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_391 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_394 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_397 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 exfalso;lia.
Qed.
