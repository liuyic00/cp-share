From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model GlobalStable GlobalInstances GlobalProgressTypes GlobalInitialLocal GlobalInitialTypes.
Local Open Scope N_scope.
Lemma global_initial_type_chunk_2 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 forall index,(Nat.le 400 index /\ Nat.lt index 600) ->
 global_port_at index=true -> option_map type_of_val(global_value_at index states)=Some(Gtyp(global_type_at index)).
Proof.
 intros index Range.
 remember (Nat.sub index 400) as offset eqn:Offset.
 have Index:index=Nat.add 400 offset by lia.
 have Bound:(offset < 200)%coq_nat by lia.
 rewrite Index.
 destruct offset as [|offset].
 - intro included. exact(initial_type_400 v previous external states ports ran).
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
 - intro included. exact(initial_type_411 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_414 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_418 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_421 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_425 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_428 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_431 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_434 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_437 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_439 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_442 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_444 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_447 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_449 v previous external states ports ran).
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
 - intro included. exact(initial_type_460 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_463 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_466 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_469 v previous external states ports ran).
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
 - intro included. exact(initial_type_480 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_483 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_487 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_490 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_494 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_497 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_500 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_503 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_506 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_508 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_511 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_513 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_516 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_518 v previous external states ports ran).
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
 - intro included. exact(initial_type_529 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_532 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_535 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_538 v previous external states ports ran).
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
 - intro included. exact(initial_type_549 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_552 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_556 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_559 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_563 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_566 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_569 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_572 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_575 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_577 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_580 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_582 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_585 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_587 v previous external states ports ran).
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
 - intro included. exact(initial_type_598 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 exfalso;lia.
Qed.
