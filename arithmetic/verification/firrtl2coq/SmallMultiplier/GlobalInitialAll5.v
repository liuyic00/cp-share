From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model GlobalStable GlobalInstances GlobalProgressTypes GlobalInitialLocal GlobalInitialTypes.
Local Open Scope N_scope.
Lemma global_initial_type_chunk_5 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 forall index,(Nat.le 1000 index /\ Nat.lt index 1200) ->
 global_port_at index=true -> option_map type_of_val(global_value_at index states)=Some(Gtyp(global_type_at index)).
Proof.
 intros index Range.
 remember (Nat.sub index 1000) as offset eqn:Offset.
 have Index:index=Nat.add 1000 offset by lia.
 have Bound:(offset < 200)%coq_nat by lia.
 rewrite Index.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1003 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1007 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1010 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1013 v previous external states ports ran).
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
 - intro included. exact(initial_type_1021 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1025 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1028 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1031 v previous external states ports ran).
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
 - intro included. exact(initial_type_1039 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1043 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1046 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1049 v previous external states ports ran).
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
 - intro included. exact(initial_type_1057 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1061 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1064 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1067 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1070 v previous external states ports ran).
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
 - intro included. exact(initial_type_1081 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1085 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1088 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1091 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1094 v previous external states ports ran).
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
 - intro included. exact(initial_type_1105 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1109 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1112 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1115 v previous external states ports ran).
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
 - intro included. exact(initial_type_1123 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1127 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1130 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1133 v previous external states ports ran).
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
 - intro included. exact(initial_type_1141 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1145 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1148 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1151 v previous external states ports ran).
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
 - intro included. exact(initial_type_1159 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1163 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1166 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1169 v previous external states ports ran).
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
 - intro included. exact(initial_type_1177 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1181 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1184 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1187 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1190 v previous external states ports ran).
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
 exfalso;lia.
Qed.
