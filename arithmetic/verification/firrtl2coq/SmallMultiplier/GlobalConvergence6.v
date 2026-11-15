From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalProgressTypes GlobalFieldSteps GlobalScalarSteps GlobalProgress.
Local Open Scope N_scope.
From SmallMultiplier Require Import GlobalTypeProgress.
Lemma global_rank_chunk_6 invalid snapshot final v level (prior:global_ranked v level snapshot) (sizes:global_leaf_sizes v)
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 List.Forall (fun index => (global_rank_at index <= S level)%coq_nat -> global_value_at index final = Some (global_target_at index v)) (List.seq 1200 200).
Proof.
 constructor.
 - intro enough. exact (global_progress_1200 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1201 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1202 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1203 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1204 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1205 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1206 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1207 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1208 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1209 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1210 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1211 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1212 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1213 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1214 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1215 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1216 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1217 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1218 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1219 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1220 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1221 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1222 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1223 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1224 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1225 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1226 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1227 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1228 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1229 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1230 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1231 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1232 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1233 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1234 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1235 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1236 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1237 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1238 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1239 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1240 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1241 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1242 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1243 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1244 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1245 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1246 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1247 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1248 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1249 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1250 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1251 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1252 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1253 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1254 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1255 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1256 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1257 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1258 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1259 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1260 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1261 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1262 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1263 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1264 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1265 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1266 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1267 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1268 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1269 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1270 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1271 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1272 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1273 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1274 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1275 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1276 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1277 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1278 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1279 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1280 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1281 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1282 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1283 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1284 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1285 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1286 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1287 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1288 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1289 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1290 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1291 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1292 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1293 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1294 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1295 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1296 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1297 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1298 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1299 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1300 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1301 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1302 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1303 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1304 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1305 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1306 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1307 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1308 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1309 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1310 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1311 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1312 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1313 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1314 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1315 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1316 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1317 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1318 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1319 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1320 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1321 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1322 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1323 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1324 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1325 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1326 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1327 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1328 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1329 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1330 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1331 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1332 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1333 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1334 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1335 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1336 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1337 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1338 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1339 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1340 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1341 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1342 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1343 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1344 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1345 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1346 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1347 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1348 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1349 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1350 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1351 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1352 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1353 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1354 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1355 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1356 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1357 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1358 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1359 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1360 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1361 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1362 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1363 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1364 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1365 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1366 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1367 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1368 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1369 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1370 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1371 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1372 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1373 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1374 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1375 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1376 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1377 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1378 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1379 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1380 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1381 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1382 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1383 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1384 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1385 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1386 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1387 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1388 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1389 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1390 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1391 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1392 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1393 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1394 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1395 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1396 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1397 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1398 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1399 invalid snapshot final v level prior types sizes enough ran).
 constructor.
Qed.
Lemma global_type_chunk_6 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 List.Forall (fun index => global_port_at index=true -> option_map type_of_val (global_value_at index final)=Some(Gtyp(global_type_at index))) (List.seq 1200 200).
Proof.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1201 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1205 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1208 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1211 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1219 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1223 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1226 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1229 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1237 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1241 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1244 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1247 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1255 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1259 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1299 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1310 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1311 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1312 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1313 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1314 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1315 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1316 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1317 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1318 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1319 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1320 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1321 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1322 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1323 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1324 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1325 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1326 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1327 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1328 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1329 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1330 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1331 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1332 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1333 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1334 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1335 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1336 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1337 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1338 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1339 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1340 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1341 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1342 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1343 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1344 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1345 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1346 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1347 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1348 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1349 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1350 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1351 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1352 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1353 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1354 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1355 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1356 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1357 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1358 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1359 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1360 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1361 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1362 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1363 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1364 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1365 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1366 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1367 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1368 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1369 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
Qed.
