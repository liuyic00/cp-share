From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model GlobalStable GlobalInstances GlobalProgressTypes GlobalInitialLocal GlobalInitialTypes.
Local Open Scope N_scope.
Lemma global_initial_type_chunk_3 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 forall index,(Nat.le 600 index /\ Nat.lt index 800) ->
 global_port_at index=true -> option_map type_of_val(global_value_at index states)=Some(Gtyp(global_type_at index)).
Proof.
 intros index Range.
 remember (Nat.sub index 600) as offset eqn:Offset.
 have Index:index=Nat.add 600 offset by lia.
 have Bound:(offset < 200)%coq_nat by lia.
 rewrite Index.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_601 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_604 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_607 v previous external states ports ran).
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
 - intro included. exact(initial_type_618 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_621 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_625 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_628 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_632 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_635 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_638 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_641 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_644 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_646 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_649 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_651 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_654 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_656 v previous external states ports ran).
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
 - intro included. exact(initial_type_667 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_670 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_673 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_676 v previous external states ports ran).
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
 - intro included. exact(initial_type_687 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_690 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_694 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_697 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_701 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_704 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_707 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_710 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_713 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_715 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_718 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_720 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_723 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_725 v previous external states ports ran).
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
 - intro included. exact(initial_type_736 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_739 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_742 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_745 v previous external states ports ran).
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
 - intro included. exact(initial_type_756 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_759 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_763 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_766 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_770 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_773 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_776 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_779 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_782 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_784 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_787 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_789 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_792 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_794 v previous external states ports ran).
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
 exfalso;lia.
Qed.
