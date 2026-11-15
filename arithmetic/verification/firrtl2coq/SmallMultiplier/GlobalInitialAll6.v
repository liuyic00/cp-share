From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model GlobalStable GlobalInstances GlobalProgressTypes GlobalInitialLocal GlobalInitialTypes.
Local Open Scope N_scope.
Lemma global_initial_type_chunk_6 v previous external states
 (ports:multiplier_input_values v external)
 (ran:circuit_initial_map_with_memory generated_modules generated_top previous external=Some states) :
 forall index,(Nat.le 1200 index /\ Nat.lt index 1400) ->
 global_port_at index=true -> option_map type_of_val(global_value_at index states)=Some(Gtyp(global_type_at index)).
Proof.
 intros index Range.
 remember (Nat.sub index 1200) as offset eqn:Offset.
 have Index:index=Nat.add 1200 offset by lia.
 have Bound:(offset < 200)%coq_nat by lia.
 rewrite Index.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1201 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1205 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1208 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1211 v previous external states ports ran).
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
 - intro included. exact(initial_type_1219 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1223 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1226 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1229 v previous external states ports ran).
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
 - intro included. exact(initial_type_1237 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1241 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1244 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1247 v previous external states ports ran).
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
 - intro included. exact(initial_type_1255 v previous external states ports ran).
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro excluded. discriminate excluded.
 destruct offset as [|offset].
 - intro included. exact(initial_type_1259 v previous external states ports ran).
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
 - intro included. exact(initial_type_1299 v previous external states ports ran).
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
 - intro included. exact(initial_type_1310 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1311 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1312 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1313 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1314 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1315 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1316 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1317 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1318 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1319 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1320 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1321 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1322 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1323 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1324 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1325 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1326 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1327 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1328 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1329 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1330 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1331 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1332 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1333 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1334 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1335 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1336 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1337 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1338 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1339 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1340 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1341 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1342 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1343 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1344 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1345 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1346 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1347 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1348 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1349 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1350 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1351 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1352 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1353 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1354 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1355 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1356 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1357 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1358 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1359 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1360 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1361 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1362 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1363 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1364 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1365 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1366 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1367 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1368 v previous external states ports ran).
 destruct offset as [|offset].
 - intro included. exact(initial_type_1369 v previous external states ports ran).
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
 exfalso;lia.
Qed.
