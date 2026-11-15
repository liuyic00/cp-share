From Coq Require Import ZArith NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model GlobalStable GlobalChildren Child0Stable Child1Stable Child2Stable ChildAbstract Compressors.
Local Open Scope N_scope.
Lemma wire_alias_64 v : global_word_64 v = global_word_63 v.
Proof. have E := global_closed_64_value v.
 change (Some (Gval (Fuint 9) (global_word_63 v)) = Some (Gval (Fuint 9) (global_word_64 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_67 v : global_word_67 v = global_word_66 v.
Proof. have E := global_closed_67_value v.
 change (Some (Gval (Fuint 9) (global_word_66 v)) = Some (Gval (Fuint 9) (global_word_67 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_278 v : global_word_278 v = global_word_3 v.
Proof. have E := global_closed_278_value v.
 change (Some (Gval (Fuint 1) (global_word_3 v)) = Some (Gval (Fuint 1) (global_word_278 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_279 v : global_word_279 v = global_word_278 v. Proof. apply global_sync_279. Qed.
Lemma wire_alias_281 v : global_word_281 v = global_word_4 v.
Proof. have E := global_closed_281_value v.
 change (Some (Gval (Fuint 1) (global_word_4 v)) = Some (Gval (Fuint 1) (global_word_281 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_282 v : global_word_282 v = global_word_281 v. Proof. apply global_sync_282. Qed.
Lemma wire_alias_287 v : global_word_287 v = global_word_286 v.
Proof. have E := global_closed_287_value v.
 change (Some (Gval (Fuint 2) (global_word_286 v)) = Some (Gval (Fuint 2) (global_word_287 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_289 v : global_word_289 v = global_word_288 v.
Proof. have E := global_closed_289_value v.
 change (Some (Gval (Fuint 1) (global_word_288 v)) = Some (Gval (Fuint 1) (global_word_289 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_290 v : global_word_290 v = global_word_289 v. Proof. apply global_sync_290. Qed.
Lemma wire_alias_293 v : global_word_293 v = global_word_292 v.
Proof. have E := global_closed_293_value v.
 change (Some (Gval (Fuint 1) (global_word_292 v)) = Some (Gval (Fuint 1) (global_word_293 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_294 v : global_word_294 v = global_word_293 v. Proof. apply global_sync_294. Qed.
Lemma wire_alias_296 v : global_word_296 v = global_word_5 v.
Proof. have E := global_closed_296_value v.
 change (Some (Gval (Fuint 1) (global_word_5 v)) = Some (Gval (Fuint 1) (global_word_296 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_297 v : global_word_297 v = global_word_296 v. Proof. apply global_sync_297. Qed.
Lemma wire_alias_299 v : global_word_299 v = global_word_6 v.
Proof. have E := global_closed_299_value v.
 change (Some (Gval (Fuint 1) (global_word_6 v)) = Some (Gval (Fuint 1) (global_word_299 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_300 v : global_word_300 v = global_word_299 v. Proof. apply global_sync_300. Qed.
Lemma wire_alias_305 v : global_word_305 v = global_word_304 v.
Proof. have E := global_closed_305_value v.
 change (Some (Gval (Fuint 2) (global_word_304 v)) = Some (Gval (Fuint 2) (global_word_305 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_307 v : global_word_307 v = global_word_306 v.
Proof. have E := global_closed_307_value v.
 change (Some (Gval (Fuint 1) (global_word_306 v)) = Some (Gval (Fuint 1) (global_word_307 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_308 v : global_word_308 v = global_word_307 v. Proof. apply global_sync_308. Qed.
Lemma wire_alias_311 v : global_word_311 v = global_word_310 v.
Proof. have E := global_closed_311_value v.
 change (Some (Gval (Fuint 1) (global_word_310 v)) = Some (Gval (Fuint 1) (global_word_311 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_312 v : global_word_312 v = global_word_311 v. Proof. apply global_sync_312. Qed.
Lemma wire_alias_314 v : global_word_314 v = global_word_9 v.
Proof. have E := global_closed_314_value v.
 change (Some (Gval (Fuint 1) (global_word_9 v)) = Some (Gval (Fuint 1) (global_word_314 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_315 v : global_word_315 v = global_word_314 v. Proof. apply global_sync_315. Qed.
Lemma wire_alias_317 v : global_word_317 v = global_word_7 v.
Proof. have E := global_closed_317_value v.
 change (Some (Gval (Fuint 1) (global_word_7 v)) = Some (Gval (Fuint 1) (global_word_317 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_318 v : global_word_318 v = global_word_317 v. Proof. apply global_sync_318. Qed.
Lemma wire_alias_320 v : global_word_320 v = global_word_8 v.
Proof. have E := global_closed_320_value v.
 change (Some (Gval (Fuint 1) (global_word_8 v)) = Some (Gval (Fuint 1) (global_word_320 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_321 v : global_word_321 v = global_word_320 v. Proof. apply global_sync_321. Qed.
Lemma wire_alias_329 v : global_word_329 v = global_word_328 v.
Proof. have E := global_closed_329_value v.
 change (Some (Gval (Fuint 2) (global_word_328 v)) = Some (Gval (Fuint 2) (global_word_329 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_331 v : global_word_331 v = global_word_330 v.
Proof. have E := global_closed_331_value v.
 change (Some (Gval (Fuint 1) (global_word_330 v)) = Some (Gval (Fuint 1) (global_word_331 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_332 v : global_word_332 v = global_word_331 v. Proof. apply global_sync_332. Qed.
Lemma wire_alias_335 v : global_word_335 v = global_word_334 v.
Proof. have E := global_closed_335_value v.
 change (Some (Gval (Fuint 1) (global_word_334 v)) = Some (Gval (Fuint 1) (global_word_335 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_336 v : global_word_336 v = global_word_335 v. Proof. apply global_sync_336. Qed.
Lemma wire_alias_338 v : global_word_338 v = global_word_12 v.
Proof. have E := global_closed_338_value v.
 change (Some (Gval (Fuint 1) (global_word_12 v)) = Some (Gval (Fuint 1) (global_word_338 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_339 v : global_word_339 v = global_word_338 v. Proof. apply global_sync_339. Qed.
Lemma wire_alias_341 v : global_word_341 v = global_word_10 v.
Proof. have E := global_closed_341_value v.
 change (Some (Gval (Fuint 1) (global_word_10 v)) = Some (Gval (Fuint 1) (global_word_341 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_342 v : global_word_342 v = global_word_341 v. Proof. apply global_sync_342. Qed.
Lemma wire_alias_344 v : global_word_344 v = global_word_11 v.
Proof. have E := global_closed_344_value v.
 change (Some (Gval (Fuint 1) (global_word_11 v)) = Some (Gval (Fuint 1) (global_word_344 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_345 v : global_word_345 v = global_word_344 v. Proof. apply global_sync_345. Qed.
Lemma wire_alias_353 v : global_word_353 v = global_word_352 v.
Proof. have E := global_closed_353_value v.
 change (Some (Gval (Fuint 2) (global_word_352 v)) = Some (Gval (Fuint 2) (global_word_353 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_355 v : global_word_355 v = global_word_354 v.
Proof. have E := global_closed_355_value v.
 change (Some (Gval (Fuint 1) (global_word_354 v)) = Some (Gval (Fuint 1) (global_word_355 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_356 v : global_word_356 v = global_word_355 v. Proof. apply global_sync_356. Qed.
Lemma wire_alias_359 v : global_word_359 v = global_word_358 v.
Proof. have E := global_closed_359_value v.
 change (Some (Gval (Fuint 1) (global_word_358 v)) = Some (Gval (Fuint 1) (global_word_359 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_360 v : global_word_360 v = global_word_359 v. Proof. apply global_sync_360. Qed.
Lemma wire_alias_363 v : global_word_363 v = global_word_362 v. Proof. apply global_sync_363. Qed.
Lemma wire_alias_364 v : global_word_364 v = global_word_363 v.
Proof. have E := global_closed_364_value v.
 change (Some (Gval (Fuint 1) (global_word_363 v)) = Some (Gval (Fuint 1) (global_word_364 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_365 v : global_word_365 v = global_word_364 v.
Proof. have E := global_closed_365_value v.
 change (Some (Gval (Fuint 1) (global_word_364 v)) = Some (Gval (Fuint 1) (global_word_365 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_366 v : global_word_366 v = global_word_365 v. Proof. apply global_sync_366. Qed.
Lemma wire_alias_368 v : global_word_368 v = global_word_15 v.
Proof. have E := global_closed_368_value v.
 change (Some (Gval (Fuint 1) (global_word_15 v)) = Some (Gval (Fuint 1) (global_word_368 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_369 v : global_word_369 v = global_word_368 v. Proof. apply global_sync_369. Qed.
Lemma wire_alias_370 v : global_word_370 v = global_word_369 v.
Proof. have E := global_closed_370_value v.
 change (Some (Gval (Fuint 1) (global_word_369 v)) = Some (Gval (Fuint 1) (global_word_370 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_371 v : global_word_371 v = global_word_370 v. Proof. apply global_sync_371. Qed.
Lemma wire_alias_373 v : global_word_373 v = global_word_13 v.
Proof. have E := global_closed_373_value v.
 change (Some (Gval (Fuint 1) (global_word_13 v)) = Some (Gval (Fuint 1) (global_word_373 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_374 v : global_word_374 v = global_word_373 v. Proof. apply global_sync_374. Qed.
Lemma wire_alias_375 v : global_word_375 v = global_word_374 v.
Proof. have E := global_closed_375_value v.
 change (Some (Gval (Fuint 1) (global_word_374 v)) = Some (Gval (Fuint 1) (global_word_375 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_376 v : global_word_376 v = global_word_375 v. Proof. apply global_sync_376. Qed.
Lemma wire_alias_378 v : global_word_378 v = global_word_14 v.
Proof. have E := global_closed_378_value v.
 change (Some (Gval (Fuint 1) (global_word_14 v)) = Some (Gval (Fuint 1) (global_word_378 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_379 v : global_word_379 v = global_word_378 v. Proof. apply global_sync_379. Qed.
Lemma wire_alias_380 v : global_word_380 v = global_word_379 v.
Proof. have E := global_closed_380_value v.
 change (Some (Gval (Fuint 1) (global_word_379 v)) = Some (Gval (Fuint 1) (global_word_380 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_381 v : global_word_381 v = global_word_380 v. Proof. apply global_sync_381. Qed.
Lemma wire_alias_389 v : global_word_389 v = global_word_388 v.
Proof. have E := global_closed_389_value v.
 change (Some (Gval (Fuint 2) (global_word_388 v)) = Some (Gval (Fuint 2) (global_word_389 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_391 v : global_word_391 v = global_word_390 v.
Proof. have E := global_closed_391_value v.
 change (Some (Gval (Fuint 1) (global_word_390 v)) = Some (Gval (Fuint 1) (global_word_391 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_392 v : global_word_392 v = global_word_391 v. Proof. apply global_sync_392. Qed.
Lemma wire_alias_393 v : global_word_393 v = global_word_392 v.
Proof. have E := global_closed_393_value v.
 change (Some (Gval (Fuint 1) (global_word_392 v)) = Some (Gval (Fuint 1) (global_word_393 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_394 v : global_word_394 v = global_word_393 v.
Proof. have E := global_closed_394_value v.
 change (Some (Gval (Fuint 1) (global_word_393 v)) = Some (Gval (Fuint 1) (global_word_394 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_395 v : global_word_395 v = global_word_394 v. Proof. apply global_sync_395. Qed.
Lemma wire_alias_397 v : global_word_397 v = global_word_16 v.
Proof. have E := global_closed_397_value v.
 change (Some (Gval (Fuint 1) (global_word_16 v)) = Some (Gval (Fuint 1) (global_word_397 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_398 v : global_word_398 v = global_word_397 v. Proof. apply global_sync_398. Qed.
Lemma wire_alias_399 v : global_word_399 v = global_word_398 v.
Proof. have E := global_closed_399_value v.
 change (Some (Gval (Fuint 1) (global_word_398 v)) = Some (Gval (Fuint 1) (global_word_399 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_400 v : global_word_400 v = global_word_399 v.
Proof. have E := global_closed_400_value v.
 change (Some (Gval (Fuint 1) (global_word_399 v)) = Some (Gval (Fuint 1) (global_word_400 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_401 v : global_word_401 v = global_word_400 v. Proof. apply global_sync_401. Qed.
Lemma wire_alias_409 v : global_word_409 v = global_word_408 v.
Proof. have E := global_closed_409_value v.
 change (Some (Gval (Fuint 2) (global_word_408 v)) = Some (Gval (Fuint 2) (global_word_409 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_411 v : global_word_411 v = global_word_410 v.
Proof. have E := global_closed_411_value v.
 change (Some (Gval (Fuint 1) (global_word_410 v)) = Some (Gval (Fuint 1) (global_word_411 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_412 v : global_word_412 v = global_word_411 v. Proof. apply global_sync_412. Qed.
Lemma wire_alias_413 v : global_word_413 v = global_word_412 v.
Proof. have E := global_closed_413_value v.
 change (Some (Gval (Fuint 1) (global_word_412 v)) = Some (Gval (Fuint 1) (global_word_413 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_414 v : global_word_414 v = global_word_413 v.
Proof. have E := global_closed_414_value v.
 change (Some (Gval (Fuint 1) (global_word_413 v)) = Some (Gval (Fuint 1) (global_word_414 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_415 v : global_word_415 v = global_word_414 v. Proof. apply global_sync_415. Qed.
Lemma wire_alias_418 v : global_word_418 v = global_word_417 v.
Proof. have E := global_closed_418_value v.
 change (Some (Gval (Fuint 1) (global_word_417 v)) = Some (Gval (Fuint 1) (global_word_418 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_419 v : global_word_419 v = global_word_418 v. Proof. apply global_sync_419. Qed.
Lemma wire_alias_420 v : global_word_420 v = global_word_419 v.
Proof. have E := global_closed_420_value v.
 change (Some (Gval (Fuint 1) (global_word_419 v)) = Some (Gval (Fuint 1) (global_word_420 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_421 v : global_word_421 v = global_word_420 v.
Proof. have E := global_closed_421_value v.
 change (Some (Gval (Fuint 1) (global_word_420 v)) = Some (Gval (Fuint 1) (global_word_421 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_422 v : global_word_422 v = global_word_421 v. Proof. apply global_sync_422. Qed.
Lemma wire_alias_425 v : global_word_425 v = global_word_424 v.
Proof. have E := global_closed_425_value v.
 change (Some (Gval (Fuint 1) (global_word_424 v)) = Some (Gval (Fuint 1) (global_word_425 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_426 v : global_word_426 v = global_word_425 v. Proof. apply global_sync_426. Qed.
Lemma wire_alias_427 v : global_word_427 v = global_word_426 v.
Proof. have E := global_closed_427_value v.
 change (Some (Gval (Fuint 1) (global_word_426 v)) = Some (Gval (Fuint 1) (global_word_427 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_428 v : global_word_428 v = global_word_427 v.
Proof. have E := global_closed_428_value v.
 change (Some (Gval (Fuint 1) (global_word_427 v)) = Some (Gval (Fuint 1) (global_word_428 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_429 v : global_word_429 v = global_word_428 v. Proof. apply global_sync_429. Qed.
Lemma wire_alias_431 v : global_word_431 v = global_word_423 v.
Proof. have E := global_closed_431_value v.
 change (Some (Gval (Fuint 1) (global_word_423 v)) = Some (Gval (Fuint 1) (global_word_431 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_432 v : global_word_432 v = global_word_431 v. Proof. apply global_sync_432. Qed.
Lemma wire_alias_433 v : global_word_433 v = global_word_432 v.
Proof. have E := global_closed_433_value v.
 change (Some (Gval (Fuint 1) (global_word_432 v)) = Some (Gval (Fuint 1) (global_word_433 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_434 v : global_word_434 v = global_word_433 v.
Proof. have E := global_closed_434_value v.
 change (Some (Gval (Fuint 1) (global_word_433 v)) = Some (Gval (Fuint 1) (global_word_434 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_435 v : global_word_435 v = global_word_434 v. Proof. apply global_sync_435. Qed.
Lemma wire_alias_437 v : global_word_437 v = global_word_19 v.
Proof. have E := global_closed_437_value v.
 change (Some (Gval (Fuint 1) (global_word_19 v)) = Some (Gval (Fuint 1) (global_word_437 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_438 v : global_word_438 v = global_word_437 v. Proof. apply global_sync_438. Qed.
Lemma wire_alias_439 v : global_word_439 v = global_word_438 v.
Proof. have E := global_closed_439_value v.
 change (Some (Gval (Fuint 1) (global_word_438 v)) = Some (Gval (Fuint 1) (global_word_439 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_440 v : global_word_440 v = global_word_439 v. Proof. apply global_sync_440. Qed.
Lemma wire_alias_442 v : global_word_442 v = global_word_17 v.
Proof. have E := global_closed_442_value v.
 change (Some (Gval (Fuint 1) (global_word_17 v)) = Some (Gval (Fuint 1) (global_word_442 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_443 v : global_word_443 v = global_word_442 v. Proof. apply global_sync_443. Qed.
Lemma wire_alias_444 v : global_word_444 v = global_word_443 v.
Proof. have E := global_closed_444_value v.
 change (Some (Gval (Fuint 1) (global_word_443 v)) = Some (Gval (Fuint 1) (global_word_444 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_445 v : global_word_445 v = global_word_444 v. Proof. apply global_sync_445. Qed.
Lemma wire_alias_447 v : global_word_447 v = global_word_18 v.
Proof. have E := global_closed_447_value v.
 change (Some (Gval (Fuint 1) (global_word_18 v)) = Some (Gval (Fuint 1) (global_word_447 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_448 v : global_word_448 v = global_word_447 v. Proof. apply global_sync_448. Qed.
Lemma wire_alias_449 v : global_word_449 v = global_word_448 v.
Proof. have E := global_closed_449_value v.
 change (Some (Gval (Fuint 1) (global_word_448 v)) = Some (Gval (Fuint 1) (global_word_449 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_450 v : global_word_450 v = global_word_449 v. Proof. apply global_sync_450. Qed.
Lemma wire_alias_458 v : global_word_458 v = global_word_457 v.
Proof. have E := global_closed_458_value v.
 change (Some (Gval (Fuint 2) (global_word_457 v)) = Some (Gval (Fuint 2) (global_word_458 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_460 v : global_word_460 v = global_word_459 v.
Proof. have E := global_closed_460_value v.
 change (Some (Gval (Fuint 1) (global_word_459 v)) = Some (Gval (Fuint 1) (global_word_460 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_461 v : global_word_461 v = global_word_460 v. Proof. apply global_sync_461. Qed.
Lemma wire_alias_462 v : global_word_462 v = global_word_461 v.
Proof. have E := global_closed_462_value v.
 change (Some (Gval (Fuint 1) (global_word_461 v)) = Some (Gval (Fuint 1) (global_word_462 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_463 v : global_word_463 v = global_word_462 v.
Proof. have E := global_closed_463_value v.
 change (Some (Gval (Fuint 1) (global_word_462 v)) = Some (Gval (Fuint 1) (global_word_463 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_464 v : global_word_464 v = global_word_463 v. Proof. apply global_sync_464. Qed.
Lemma wire_alias_466 v : global_word_466 v = global_word_20 v.
Proof. have E := global_closed_466_value v.
 change (Some (Gval (Fuint 1) (global_word_20 v)) = Some (Gval (Fuint 1) (global_word_466 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_467 v : global_word_467 v = global_word_466 v. Proof. apply global_sync_467. Qed.
Lemma wire_alias_468 v : global_word_468 v = global_word_467 v.
Proof. have E := global_closed_468_value v.
 change (Some (Gval (Fuint 1) (global_word_467 v)) = Some (Gval (Fuint 1) (global_word_468 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_469 v : global_word_469 v = global_word_468 v.
Proof. have E := global_closed_469_value v.
 change (Some (Gval (Fuint 1) (global_word_468 v)) = Some (Gval (Fuint 1) (global_word_469 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_470 v : global_word_470 v = global_word_469 v. Proof. apply global_sync_470. Qed.
Lemma wire_alias_478 v : global_word_478 v = global_word_477 v.
Proof. have E := global_closed_478_value v.
 change (Some (Gval (Fuint 2) (global_word_477 v)) = Some (Gval (Fuint 2) (global_word_478 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_480 v : global_word_480 v = global_word_479 v.
Proof. have E := global_closed_480_value v.
 change (Some (Gval (Fuint 1) (global_word_479 v)) = Some (Gval (Fuint 1) (global_word_480 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_481 v : global_word_481 v = global_word_480 v. Proof. apply global_sync_481. Qed.
Lemma wire_alias_482 v : global_word_482 v = global_word_481 v.
Proof. have E := global_closed_482_value v.
 change (Some (Gval (Fuint 1) (global_word_481 v)) = Some (Gval (Fuint 1) (global_word_482 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_483 v : global_word_483 v = global_word_482 v.
Proof. have E := global_closed_483_value v.
 change (Some (Gval (Fuint 1) (global_word_482 v)) = Some (Gval (Fuint 1) (global_word_483 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_484 v : global_word_484 v = global_word_483 v. Proof. apply global_sync_484. Qed.
Lemma wire_alias_487 v : global_word_487 v = global_word_486 v.
Proof. have E := global_closed_487_value v.
 change (Some (Gval (Fuint 1) (global_word_486 v)) = Some (Gval (Fuint 1) (global_word_487 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_488 v : global_word_488 v = global_word_487 v. Proof. apply global_sync_488. Qed.
Lemma wire_alias_489 v : global_word_489 v = global_word_488 v.
Proof. have E := global_closed_489_value v.
 change (Some (Gval (Fuint 1) (global_word_488 v)) = Some (Gval (Fuint 1) (global_word_489 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_490 v : global_word_490 v = global_word_489 v.
Proof. have E := global_closed_490_value v.
 change (Some (Gval (Fuint 1) (global_word_489 v)) = Some (Gval (Fuint 1) (global_word_490 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_491 v : global_word_491 v = global_word_490 v. Proof. apply global_sync_491. Qed.
Lemma wire_alias_494 v : global_word_494 v = global_word_493 v.
Proof. have E := global_closed_494_value v.
 change (Some (Gval (Fuint 1) (global_word_493 v)) = Some (Gval (Fuint 1) (global_word_494 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_495 v : global_word_495 v = global_word_494 v. Proof. apply global_sync_495. Qed.
Lemma wire_alias_496 v : global_word_496 v = global_word_495 v.
Proof. have E := global_closed_496_value v.
 change (Some (Gval (Fuint 1) (global_word_495 v)) = Some (Gval (Fuint 1) (global_word_496 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_497 v : global_word_497 v = global_word_496 v.
Proof. have E := global_closed_497_value v.
 change (Some (Gval (Fuint 1) (global_word_496 v)) = Some (Gval (Fuint 1) (global_word_497 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_498 v : global_word_498 v = global_word_497 v. Proof. apply global_sync_498. Qed.
Lemma wire_alias_500 v : global_word_500 v = global_word_492 v.
Proof. have E := global_closed_500_value v.
 change (Some (Gval (Fuint 1) (global_word_492 v)) = Some (Gval (Fuint 1) (global_word_500 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_501 v : global_word_501 v = global_word_500 v. Proof. apply global_sync_501. Qed.
Lemma wire_alias_502 v : global_word_502 v = global_word_501 v.
Proof. have E := global_closed_502_value v.
 change (Some (Gval (Fuint 1) (global_word_501 v)) = Some (Gval (Fuint 1) (global_word_502 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_503 v : global_word_503 v = global_word_502 v.
Proof. have E := global_closed_503_value v.
 change (Some (Gval (Fuint 1) (global_word_502 v)) = Some (Gval (Fuint 1) (global_word_503 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_504 v : global_word_504 v = global_word_503 v. Proof. apply global_sync_504. Qed.
Lemma wire_alias_506 v : global_word_506 v = global_word_23 v.
Proof. have E := global_closed_506_value v.
 change (Some (Gval (Fuint 1) (global_word_23 v)) = Some (Gval (Fuint 1) (global_word_506 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_507 v : global_word_507 v = global_word_506 v. Proof. apply global_sync_507. Qed.
Lemma wire_alias_508 v : global_word_508 v = global_word_507 v.
Proof. have E := global_closed_508_value v.
 change (Some (Gval (Fuint 1) (global_word_507 v)) = Some (Gval (Fuint 1) (global_word_508 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_509 v : global_word_509 v = global_word_508 v. Proof. apply global_sync_509. Qed.
Lemma wire_alias_511 v : global_word_511 v = global_word_21 v.
Proof. have E := global_closed_511_value v.
 change (Some (Gval (Fuint 1) (global_word_21 v)) = Some (Gval (Fuint 1) (global_word_511 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_512 v : global_word_512 v = global_word_511 v. Proof. apply global_sync_512. Qed.
Lemma wire_alias_513 v : global_word_513 v = global_word_512 v.
Proof. have E := global_closed_513_value v.
 change (Some (Gval (Fuint 1) (global_word_512 v)) = Some (Gval (Fuint 1) (global_word_513 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_514 v : global_word_514 v = global_word_513 v. Proof. apply global_sync_514. Qed.
Lemma wire_alias_516 v : global_word_516 v = global_word_22 v.
Proof. have E := global_closed_516_value v.
 change (Some (Gval (Fuint 1) (global_word_22 v)) = Some (Gval (Fuint 1) (global_word_516 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_517 v : global_word_517 v = global_word_516 v. Proof. apply global_sync_517. Qed.
Lemma wire_alias_518 v : global_word_518 v = global_word_517 v.
Proof. have E := global_closed_518_value v.
 change (Some (Gval (Fuint 1) (global_word_517 v)) = Some (Gval (Fuint 1) (global_word_518 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_519 v : global_word_519 v = global_word_518 v. Proof. apply global_sync_519. Qed.
Lemma wire_alias_527 v : global_word_527 v = global_word_526 v.
Proof. have E := global_closed_527_value v.
 change (Some (Gval (Fuint 2) (global_word_526 v)) = Some (Gval (Fuint 2) (global_word_527 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_529 v : global_word_529 v = global_word_528 v.
Proof. have E := global_closed_529_value v.
 change (Some (Gval (Fuint 1) (global_word_528 v)) = Some (Gval (Fuint 1) (global_word_529 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_530 v : global_word_530 v = global_word_529 v. Proof. apply global_sync_530. Qed.
Lemma wire_alias_531 v : global_word_531 v = global_word_530 v.
Proof. have E := global_closed_531_value v.
 change (Some (Gval (Fuint 1) (global_word_530 v)) = Some (Gval (Fuint 1) (global_word_531 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_532 v : global_word_532 v = global_word_531 v.
Proof. have E := global_closed_532_value v.
 change (Some (Gval (Fuint 1) (global_word_531 v)) = Some (Gval (Fuint 1) (global_word_532 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_533 v : global_word_533 v = global_word_532 v. Proof. apply global_sync_533. Qed.
Lemma wire_alias_535 v : global_word_535 v = global_word_24 v.
Proof. have E := global_closed_535_value v.
 change (Some (Gval (Fuint 1) (global_word_24 v)) = Some (Gval (Fuint 1) (global_word_535 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_536 v : global_word_536 v = global_word_535 v. Proof. apply global_sync_536. Qed.
Lemma wire_alias_537 v : global_word_537 v = global_word_536 v.
Proof. have E := global_closed_537_value v.
 change (Some (Gval (Fuint 1) (global_word_536 v)) = Some (Gval (Fuint 1) (global_word_537 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_538 v : global_word_538 v = global_word_537 v.
Proof. have E := global_closed_538_value v.
 change (Some (Gval (Fuint 1) (global_word_537 v)) = Some (Gval (Fuint 1) (global_word_538 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_539 v : global_word_539 v = global_word_538 v. Proof. apply global_sync_539. Qed.
Lemma wire_alias_547 v : global_word_547 v = global_word_546 v.
Proof. have E := global_closed_547_value v.
 change (Some (Gval (Fuint 2) (global_word_546 v)) = Some (Gval (Fuint 2) (global_word_547 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_549 v : global_word_549 v = global_word_548 v.
Proof. have E := global_closed_549_value v.
 change (Some (Gval (Fuint 1) (global_word_548 v)) = Some (Gval (Fuint 1) (global_word_549 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_550 v : global_word_550 v = global_word_549 v. Proof. apply global_sync_550. Qed.
Lemma wire_alias_551 v : global_word_551 v = global_word_550 v.
Proof. have E := global_closed_551_value v.
 change (Some (Gval (Fuint 1) (global_word_550 v)) = Some (Gval (Fuint 1) (global_word_551 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_552 v : global_word_552 v = global_word_551 v.
Proof. have E := global_closed_552_value v.
 change (Some (Gval (Fuint 1) (global_word_551 v)) = Some (Gval (Fuint 1) (global_word_552 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_553 v : global_word_553 v = global_word_552 v. Proof. apply global_sync_553. Qed.
Lemma wire_alias_556 v : global_word_556 v = global_word_555 v.
Proof. have E := global_closed_556_value v.
 change (Some (Gval (Fuint 1) (global_word_555 v)) = Some (Gval (Fuint 1) (global_word_556 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_557 v : global_word_557 v = global_word_556 v. Proof. apply global_sync_557. Qed.
Lemma wire_alias_558 v : global_word_558 v = global_word_557 v.
Proof. have E := global_closed_558_value v.
 change (Some (Gval (Fuint 1) (global_word_557 v)) = Some (Gval (Fuint 1) (global_word_558 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_559 v : global_word_559 v = global_word_558 v.
Proof. have E := global_closed_559_value v.
 change (Some (Gval (Fuint 1) (global_word_558 v)) = Some (Gval (Fuint 1) (global_word_559 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_560 v : global_word_560 v = global_word_559 v. Proof. apply global_sync_560. Qed.
Lemma wire_alias_563 v : global_word_563 v = global_word_562 v.
Proof. have E := global_closed_563_value v.
 change (Some (Gval (Fuint 1) (global_word_562 v)) = Some (Gval (Fuint 1) (global_word_563 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_564 v : global_word_564 v = global_word_563 v. Proof. apply global_sync_564. Qed.
Lemma wire_alias_565 v : global_word_565 v = global_word_564 v.
Proof. have E := global_closed_565_value v.
 change (Some (Gval (Fuint 1) (global_word_564 v)) = Some (Gval (Fuint 1) (global_word_565 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_566 v : global_word_566 v = global_word_565 v.
Proof. have E := global_closed_566_value v.
 change (Some (Gval (Fuint 1) (global_word_565 v)) = Some (Gval (Fuint 1) (global_word_566 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_567 v : global_word_567 v = global_word_566 v. Proof. apply global_sync_567. Qed.
Lemma wire_alias_569 v : global_word_569 v = global_word_561 v.
Proof. have E := global_closed_569_value v.
 change (Some (Gval (Fuint 1) (global_word_561 v)) = Some (Gval (Fuint 1) (global_word_569 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_570 v : global_word_570 v = global_word_569 v. Proof. apply global_sync_570. Qed.
Lemma wire_alias_571 v : global_word_571 v = global_word_570 v.
Proof. have E := global_closed_571_value v.
 change (Some (Gval (Fuint 1) (global_word_570 v)) = Some (Gval (Fuint 1) (global_word_571 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_572 v : global_word_572 v = global_word_571 v.
Proof. have E := global_closed_572_value v.
 change (Some (Gval (Fuint 1) (global_word_571 v)) = Some (Gval (Fuint 1) (global_word_572 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_573 v : global_word_573 v = global_word_572 v. Proof. apply global_sync_573. Qed.
Lemma wire_alias_575 v : global_word_575 v = global_word_28 v.
Proof. have E := global_closed_575_value v.
 change (Some (Gval (Fuint 1) (global_word_28 v)) = Some (Gval (Fuint 1) (global_word_575 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_576 v : global_word_576 v = global_word_575 v. Proof. apply global_sync_576. Qed.
Lemma wire_alias_577 v : global_word_577 v = global_word_576 v.
Proof. have E := global_closed_577_value v.
 change (Some (Gval (Fuint 1) (global_word_576 v)) = Some (Gval (Fuint 1) (global_word_577 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_578 v : global_word_578 v = global_word_577 v. Proof. apply global_sync_578. Qed.
Lemma wire_alias_580 v : global_word_580 v = global_word_26 v.
Proof. have E := global_closed_580_value v.
 change (Some (Gval (Fuint 1) (global_word_26 v)) = Some (Gval (Fuint 1) (global_word_580 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_581 v : global_word_581 v = global_word_580 v. Proof. apply global_sync_581. Qed.
Lemma wire_alias_582 v : global_word_582 v = global_word_581 v.
Proof. have E := global_closed_582_value v.
 change (Some (Gval (Fuint 1) (global_word_581 v)) = Some (Gval (Fuint 1) (global_word_582 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_583 v : global_word_583 v = global_word_582 v. Proof. apply global_sync_583. Qed.
Lemma wire_alias_585 v : global_word_585 v = global_word_27 v.
Proof. have E := global_closed_585_value v.
 change (Some (Gval (Fuint 1) (global_word_27 v)) = Some (Gval (Fuint 1) (global_word_585 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_586 v : global_word_586 v = global_word_585 v. Proof. apply global_sync_586. Qed.
Lemma wire_alias_587 v : global_word_587 v = global_word_586 v.
Proof. have E := global_closed_587_value v.
 change (Some (Gval (Fuint 1) (global_word_586 v)) = Some (Gval (Fuint 1) (global_word_587 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_588 v : global_word_588 v = global_word_587 v. Proof. apply global_sync_588. Qed.
Lemma wire_alias_596 v : global_word_596 v = global_word_595 v.
Proof. have E := global_closed_596_value v.
 change (Some (Gval (Fuint 2) (global_word_595 v)) = Some (Gval (Fuint 2) (global_word_596 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_598 v : global_word_598 v = global_word_597 v.
Proof. have E := global_closed_598_value v.
 change (Some (Gval (Fuint 1) (global_word_597 v)) = Some (Gval (Fuint 1) (global_word_598 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_599 v : global_word_599 v = global_word_598 v. Proof. apply global_sync_599. Qed.
Lemma wire_alias_600 v : global_word_600 v = global_word_599 v.
Proof. have E := global_closed_600_value v.
 change (Some (Gval (Fuint 1) (global_word_599 v)) = Some (Gval (Fuint 1) (global_word_600 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_601 v : global_word_601 v = global_word_600 v.
Proof. have E := global_closed_601_value v.
 change (Some (Gval (Fuint 1) (global_word_600 v)) = Some (Gval (Fuint 1) (global_word_601 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_602 v : global_word_602 v = global_word_601 v. Proof. apply global_sync_602. Qed.
Lemma wire_alias_604 v : global_word_604 v = global_word_29 v.
Proof. have E := global_closed_604_value v.
 change (Some (Gval (Fuint 1) (global_word_29 v)) = Some (Gval (Fuint 1) (global_word_604 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_605 v : global_word_605 v = global_word_604 v. Proof. apply global_sync_605. Qed.
Lemma wire_alias_606 v : global_word_606 v = global_word_605 v.
Proof. have E := global_closed_606_value v.
 change (Some (Gval (Fuint 1) (global_word_605 v)) = Some (Gval (Fuint 1) (global_word_606 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_607 v : global_word_607 v = global_word_606 v.
Proof. have E := global_closed_607_value v.
 change (Some (Gval (Fuint 1) (global_word_606 v)) = Some (Gval (Fuint 1) (global_word_607 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_608 v : global_word_608 v = global_word_607 v. Proof. apply global_sync_608. Qed.
Lemma wire_alias_616 v : global_word_616 v = global_word_615 v.
Proof. have E := global_closed_616_value v.
 change (Some (Gval (Fuint 2) (global_word_615 v)) = Some (Gval (Fuint 2) (global_word_616 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_618 v : global_word_618 v = global_word_617 v.
Proof. have E := global_closed_618_value v.
 change (Some (Gval (Fuint 1) (global_word_617 v)) = Some (Gval (Fuint 1) (global_word_618 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_619 v : global_word_619 v = global_word_618 v. Proof. apply global_sync_619. Qed.
Lemma wire_alias_620 v : global_word_620 v = global_word_619 v.
Proof. have E := global_closed_620_value v.
 change (Some (Gval (Fuint 1) (global_word_619 v)) = Some (Gval (Fuint 1) (global_word_620 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_621 v : global_word_621 v = global_word_620 v.
Proof. have E := global_closed_621_value v.
 change (Some (Gval (Fuint 1) (global_word_620 v)) = Some (Gval (Fuint 1) (global_word_621 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_622 v : global_word_622 v = global_word_621 v. Proof. apply global_sync_622. Qed.
Lemma wire_alias_625 v : global_word_625 v = global_word_624 v.
Proof. have E := global_closed_625_value v.
 change (Some (Gval (Fuint 1) (global_word_624 v)) = Some (Gval (Fuint 1) (global_word_625 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_626 v : global_word_626 v = global_word_625 v. Proof. apply global_sync_626. Qed.
Lemma wire_alias_627 v : global_word_627 v = global_word_626 v.
Proof. have E := global_closed_627_value v.
 change (Some (Gval (Fuint 1) (global_word_626 v)) = Some (Gval (Fuint 1) (global_word_627 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_628 v : global_word_628 v = global_word_627 v.
Proof. have E := global_closed_628_value v.
 change (Some (Gval (Fuint 1) (global_word_627 v)) = Some (Gval (Fuint 1) (global_word_628 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_629 v : global_word_629 v = global_word_628 v. Proof. apply global_sync_629. Qed.
Lemma wire_alias_632 v : global_word_632 v = global_word_631 v.
Proof. have E := global_closed_632_value v.
 change (Some (Gval (Fuint 1) (global_word_631 v)) = Some (Gval (Fuint 1) (global_word_632 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_633 v : global_word_633 v = global_word_632 v. Proof. apply global_sync_633. Qed.
Lemma wire_alias_634 v : global_word_634 v = global_word_633 v.
Proof. have E := global_closed_634_value v.
 change (Some (Gval (Fuint 1) (global_word_633 v)) = Some (Gval (Fuint 1) (global_word_634 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_635 v : global_word_635 v = global_word_634 v.
Proof. have E := global_closed_635_value v.
 change (Some (Gval (Fuint 1) (global_word_634 v)) = Some (Gval (Fuint 1) (global_word_635 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_636 v : global_word_636 v = global_word_635 v. Proof. apply global_sync_636. Qed.
Lemma wire_alias_638 v : global_word_638 v = global_word_630 v.
Proof. have E := global_closed_638_value v.
 change (Some (Gval (Fuint 1) (global_word_630 v)) = Some (Gval (Fuint 1) (global_word_638 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_639 v : global_word_639 v = global_word_638 v. Proof. apply global_sync_639. Qed.
Lemma wire_alias_640 v : global_word_640 v = global_word_639 v.
Proof. have E := global_closed_640_value v.
 change (Some (Gval (Fuint 1) (global_word_639 v)) = Some (Gval (Fuint 1) (global_word_640 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_641 v : global_word_641 v = global_word_640 v.
Proof. have E := global_closed_641_value v.
 change (Some (Gval (Fuint 1) (global_word_640 v)) = Some (Gval (Fuint 1) (global_word_641 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_642 v : global_word_642 v = global_word_641 v. Proof. apply global_sync_642. Qed.
Lemma wire_alias_644 v : global_word_644 v = global_word_33 v.
Proof. have E := global_closed_644_value v.
 change (Some (Gval (Fuint 1) (global_word_33 v)) = Some (Gval (Fuint 1) (global_word_644 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_645 v : global_word_645 v = global_word_644 v. Proof. apply global_sync_645. Qed.
Lemma wire_alias_646 v : global_word_646 v = global_word_645 v.
Proof. have E := global_closed_646_value v.
 change (Some (Gval (Fuint 1) (global_word_645 v)) = Some (Gval (Fuint 1) (global_word_646 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_647 v : global_word_647 v = global_word_646 v. Proof. apply global_sync_647. Qed.
Lemma wire_alias_649 v : global_word_649 v = global_word_31 v.
Proof. have E := global_closed_649_value v.
 change (Some (Gval (Fuint 1) (global_word_31 v)) = Some (Gval (Fuint 1) (global_word_649 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_650 v : global_word_650 v = global_word_649 v. Proof. apply global_sync_650. Qed.
Lemma wire_alias_651 v : global_word_651 v = global_word_650 v.
Proof. have E := global_closed_651_value v.
 change (Some (Gval (Fuint 1) (global_word_650 v)) = Some (Gval (Fuint 1) (global_word_651 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_652 v : global_word_652 v = global_word_651 v. Proof. apply global_sync_652. Qed.
Lemma wire_alias_654 v : global_word_654 v = global_word_32 v.
Proof. have E := global_closed_654_value v.
 change (Some (Gval (Fuint 1) (global_word_32 v)) = Some (Gval (Fuint 1) (global_word_654 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_655 v : global_word_655 v = global_word_654 v. Proof. apply global_sync_655. Qed.
Lemma wire_alias_656 v : global_word_656 v = global_word_655 v.
Proof. have E := global_closed_656_value v.
 change (Some (Gval (Fuint 1) (global_word_655 v)) = Some (Gval (Fuint 1) (global_word_656 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_657 v : global_word_657 v = global_word_656 v. Proof. apply global_sync_657. Qed.
Lemma wire_alias_665 v : global_word_665 v = global_word_664 v.
Proof. have E := global_closed_665_value v.
 change (Some (Gval (Fuint 2) (global_word_664 v)) = Some (Gval (Fuint 2) (global_word_665 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_667 v : global_word_667 v = global_word_666 v.
Proof. have E := global_closed_667_value v.
 change (Some (Gval (Fuint 1) (global_word_666 v)) = Some (Gval (Fuint 1) (global_word_667 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_668 v : global_word_668 v = global_word_667 v. Proof. apply global_sync_668. Qed.
Lemma wire_alias_669 v : global_word_669 v = global_word_668 v.
Proof. have E := global_closed_669_value v.
 change (Some (Gval (Fuint 1) (global_word_668 v)) = Some (Gval (Fuint 1) (global_word_669 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_670 v : global_word_670 v = global_word_669 v.
Proof. have E := global_closed_670_value v.
 change (Some (Gval (Fuint 1) (global_word_669 v)) = Some (Gval (Fuint 1) (global_word_670 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_671 v : global_word_671 v = global_word_670 v. Proof. apply global_sync_671. Qed.
Lemma wire_alias_673 v : global_word_673 v = global_word_34 v.
Proof. have E := global_closed_673_value v.
 change (Some (Gval (Fuint 1) (global_word_34 v)) = Some (Gval (Fuint 1) (global_word_673 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_674 v : global_word_674 v = global_word_673 v. Proof. apply global_sync_674. Qed.
Lemma wire_alias_675 v : global_word_675 v = global_word_674 v.
Proof. have E := global_closed_675_value v.
 change (Some (Gval (Fuint 1) (global_word_674 v)) = Some (Gval (Fuint 1) (global_word_675 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_676 v : global_word_676 v = global_word_675 v.
Proof. have E := global_closed_676_value v.
 change (Some (Gval (Fuint 1) (global_word_675 v)) = Some (Gval (Fuint 1) (global_word_676 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_677 v : global_word_677 v = global_word_676 v. Proof. apply global_sync_677. Qed.
Lemma wire_alias_685 v : global_word_685 v = global_word_684 v.
Proof. have E := global_closed_685_value v.
 change (Some (Gval (Fuint 2) (global_word_684 v)) = Some (Gval (Fuint 2) (global_word_685 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_687 v : global_word_687 v = global_word_686 v.
Proof. have E := global_closed_687_value v.
 change (Some (Gval (Fuint 1) (global_word_686 v)) = Some (Gval (Fuint 1) (global_word_687 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_688 v : global_word_688 v = global_word_687 v. Proof. apply global_sync_688. Qed.
Lemma wire_alias_689 v : global_word_689 v = global_word_688 v.
Proof. have E := global_closed_689_value v.
 change (Some (Gval (Fuint 1) (global_word_688 v)) = Some (Gval (Fuint 1) (global_word_689 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_690 v : global_word_690 v = global_word_689 v.
Proof. have E := global_closed_690_value v.
 change (Some (Gval (Fuint 1) (global_word_689 v)) = Some (Gval (Fuint 1) (global_word_690 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_691 v : global_word_691 v = global_word_690 v. Proof. apply global_sync_691. Qed.
Lemma wire_alias_694 v : global_word_694 v = global_word_693 v.
Proof. have E := global_closed_694_value v.
 change (Some (Gval (Fuint 1) (global_word_693 v)) = Some (Gval (Fuint 1) (global_word_694 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_695 v : global_word_695 v = global_word_694 v. Proof. apply global_sync_695. Qed.
Lemma wire_alias_696 v : global_word_696 v = global_word_695 v.
Proof. have E := global_closed_696_value v.
 change (Some (Gval (Fuint 1) (global_word_695 v)) = Some (Gval (Fuint 1) (global_word_696 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_697 v : global_word_697 v = global_word_696 v.
Proof. have E := global_closed_697_value v.
 change (Some (Gval (Fuint 1) (global_word_696 v)) = Some (Gval (Fuint 1) (global_word_697 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_698 v : global_word_698 v = global_word_697 v. Proof. apply global_sync_698. Qed.
Lemma wire_alias_701 v : global_word_701 v = global_word_700 v.
Proof. have E := global_closed_701_value v.
 change (Some (Gval (Fuint 1) (global_word_700 v)) = Some (Gval (Fuint 1) (global_word_701 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_702 v : global_word_702 v = global_word_701 v. Proof. apply global_sync_702. Qed.
Lemma wire_alias_703 v : global_word_703 v = global_word_702 v.
Proof. have E := global_closed_703_value v.
 change (Some (Gval (Fuint 1) (global_word_702 v)) = Some (Gval (Fuint 1) (global_word_703 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_704 v : global_word_704 v = global_word_703 v.
Proof. have E := global_closed_704_value v.
 change (Some (Gval (Fuint 1) (global_word_703 v)) = Some (Gval (Fuint 1) (global_word_704 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_705 v : global_word_705 v = global_word_704 v. Proof. apply global_sync_705. Qed.
Lemma wire_alias_707 v : global_word_707 v = global_word_699 v.
Proof. have E := global_closed_707_value v.
 change (Some (Gval (Fuint 1) (global_word_699 v)) = Some (Gval (Fuint 1) (global_word_707 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_708 v : global_word_708 v = global_word_707 v. Proof. apply global_sync_708. Qed.
Lemma wire_alias_709 v : global_word_709 v = global_word_708 v.
Proof. have E := global_closed_709_value v.
 change (Some (Gval (Fuint 1) (global_word_708 v)) = Some (Gval (Fuint 1) (global_word_709 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_710 v : global_word_710 v = global_word_709 v.
Proof. have E := global_closed_710_value v.
 change (Some (Gval (Fuint 1) (global_word_709 v)) = Some (Gval (Fuint 1) (global_word_710 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_711 v : global_word_711 v = global_word_710 v. Proof. apply global_sync_711. Qed.
Lemma wire_alias_713 v : global_word_713 v = global_word_37 v.
Proof. have E := global_closed_713_value v.
 change (Some (Gval (Fuint 1) (global_word_37 v)) = Some (Gval (Fuint 1) (global_word_713 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_714 v : global_word_714 v = global_word_713 v. Proof. apply global_sync_714. Qed.
Lemma wire_alias_715 v : global_word_715 v = global_word_714 v.
Proof. have E := global_closed_715_value v.
 change (Some (Gval (Fuint 1) (global_word_714 v)) = Some (Gval (Fuint 1) (global_word_715 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_716 v : global_word_716 v = global_word_715 v. Proof. apply global_sync_716. Qed.
Lemma wire_alias_718 v : global_word_718 v = global_word_35 v.
Proof. have E := global_closed_718_value v.
 change (Some (Gval (Fuint 1) (global_word_35 v)) = Some (Gval (Fuint 1) (global_word_718 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_719 v : global_word_719 v = global_word_718 v. Proof. apply global_sync_719. Qed.
Lemma wire_alias_720 v : global_word_720 v = global_word_719 v.
Proof. have E := global_closed_720_value v.
 change (Some (Gval (Fuint 1) (global_word_719 v)) = Some (Gval (Fuint 1) (global_word_720 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_721 v : global_word_721 v = global_word_720 v. Proof. apply global_sync_721. Qed.
Lemma wire_alias_723 v : global_word_723 v = global_word_36 v.
Proof. have E := global_closed_723_value v.
 change (Some (Gval (Fuint 1) (global_word_36 v)) = Some (Gval (Fuint 1) (global_word_723 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_724 v : global_word_724 v = global_word_723 v. Proof. apply global_sync_724. Qed.
Lemma wire_alias_725 v : global_word_725 v = global_word_724 v.
Proof. have E := global_closed_725_value v.
 change (Some (Gval (Fuint 1) (global_word_724 v)) = Some (Gval (Fuint 1) (global_word_725 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_726 v : global_word_726 v = global_word_725 v. Proof. apply global_sync_726. Qed.
Lemma wire_alias_734 v : global_word_734 v = global_word_733 v.
Proof. have E := global_closed_734_value v.
 change (Some (Gval (Fuint 2) (global_word_733 v)) = Some (Gval (Fuint 2) (global_word_734 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_736 v : global_word_736 v = global_word_735 v.
Proof. have E := global_closed_736_value v.
 change (Some (Gval (Fuint 1) (global_word_735 v)) = Some (Gval (Fuint 1) (global_word_736 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_737 v : global_word_737 v = global_word_736 v. Proof. apply global_sync_737. Qed.
Lemma wire_alias_738 v : global_word_738 v = global_word_737 v.
Proof. have E := global_closed_738_value v.
 change (Some (Gval (Fuint 1) (global_word_737 v)) = Some (Gval (Fuint 1) (global_word_738 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_739 v : global_word_739 v = global_word_738 v.
Proof. have E := global_closed_739_value v.
 change (Some (Gval (Fuint 1) (global_word_738 v)) = Some (Gval (Fuint 1) (global_word_739 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_740 v : global_word_740 v = global_word_739 v. Proof. apply global_sync_740. Qed.
Lemma wire_alias_742 v : global_word_742 v = global_word_38 v.
Proof. have E := global_closed_742_value v.
 change (Some (Gval (Fuint 1) (global_word_38 v)) = Some (Gval (Fuint 1) (global_word_742 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_743 v : global_word_743 v = global_word_742 v. Proof. apply global_sync_743. Qed.
Lemma wire_alias_744 v : global_word_744 v = global_word_743 v.
Proof. have E := global_closed_744_value v.
 change (Some (Gval (Fuint 1) (global_word_743 v)) = Some (Gval (Fuint 1) (global_word_744 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_745 v : global_word_745 v = global_word_744 v.
Proof. have E := global_closed_745_value v.
 change (Some (Gval (Fuint 1) (global_word_744 v)) = Some (Gval (Fuint 1) (global_word_745 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_746 v : global_word_746 v = global_word_745 v. Proof. apply global_sync_746. Qed.
Lemma wire_alias_754 v : global_word_754 v = global_word_753 v.
Proof. have E := global_closed_754_value v.
 change (Some (Gval (Fuint 2) (global_word_753 v)) = Some (Gval (Fuint 2) (global_word_754 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_756 v : global_word_756 v = global_word_755 v.
Proof. have E := global_closed_756_value v.
 change (Some (Gval (Fuint 1) (global_word_755 v)) = Some (Gval (Fuint 1) (global_word_756 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_757 v : global_word_757 v = global_word_756 v. Proof. apply global_sync_757. Qed.
Lemma wire_alias_758 v : global_word_758 v = global_word_757 v.
Proof. have E := global_closed_758_value v.
 change (Some (Gval (Fuint 1) (global_word_757 v)) = Some (Gval (Fuint 1) (global_word_758 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_759 v : global_word_759 v = global_word_758 v.
Proof. have E := global_closed_759_value v.
 change (Some (Gval (Fuint 1) (global_word_758 v)) = Some (Gval (Fuint 1) (global_word_759 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_760 v : global_word_760 v = global_word_759 v. Proof. apply global_sync_760. Qed.
Lemma wire_alias_763 v : global_word_763 v = global_word_762 v.
Proof. have E := global_closed_763_value v.
 change (Some (Gval (Fuint 1) (global_word_762 v)) = Some (Gval (Fuint 1) (global_word_763 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_764 v : global_word_764 v = global_word_763 v. Proof. apply global_sync_764. Qed.
Lemma wire_alias_765 v : global_word_765 v = global_word_764 v.
Proof. have E := global_closed_765_value v.
 change (Some (Gval (Fuint 1) (global_word_764 v)) = Some (Gval (Fuint 1) (global_word_765 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_766 v : global_word_766 v = global_word_765 v.
Proof. have E := global_closed_766_value v.
 change (Some (Gval (Fuint 1) (global_word_765 v)) = Some (Gval (Fuint 1) (global_word_766 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_767 v : global_word_767 v = global_word_766 v. Proof. apply global_sync_767. Qed.
Lemma wire_alias_770 v : global_word_770 v = global_word_769 v.
Proof. have E := global_closed_770_value v.
 change (Some (Gval (Fuint 1) (global_word_769 v)) = Some (Gval (Fuint 1) (global_word_770 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_771 v : global_word_771 v = global_word_770 v. Proof. apply global_sync_771. Qed.
Lemma wire_alias_772 v : global_word_772 v = global_word_771 v.
Proof. have E := global_closed_772_value v.
 change (Some (Gval (Fuint 1) (global_word_771 v)) = Some (Gval (Fuint 1) (global_word_772 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_773 v : global_word_773 v = global_word_772 v.
Proof. have E := global_closed_773_value v.
 change (Some (Gval (Fuint 1) (global_word_772 v)) = Some (Gval (Fuint 1) (global_word_773 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_774 v : global_word_774 v = global_word_773 v. Proof. apply global_sync_774. Qed.
Lemma wire_alias_776 v : global_word_776 v = global_word_768 v.
Proof. have E := global_closed_776_value v.
 change (Some (Gval (Fuint 1) (global_word_768 v)) = Some (Gval (Fuint 1) (global_word_776 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_777 v : global_word_777 v = global_word_776 v. Proof. apply global_sync_777. Qed.
Lemma wire_alias_778 v : global_word_778 v = global_word_777 v.
Proof. have E := global_closed_778_value v.
 change (Some (Gval (Fuint 1) (global_word_777 v)) = Some (Gval (Fuint 1) (global_word_778 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_779 v : global_word_779 v = global_word_778 v.
Proof. have E := global_closed_779_value v.
 change (Some (Gval (Fuint 1) (global_word_778 v)) = Some (Gval (Fuint 1) (global_word_779 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_780 v : global_word_780 v = global_word_779 v. Proof. apply global_sync_780. Qed.
Lemma wire_alias_782 v : global_word_782 v = global_word_41 v.
Proof. have E := global_closed_782_value v.
 change (Some (Gval (Fuint 1) (global_word_41 v)) = Some (Gval (Fuint 1) (global_word_782 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_783 v : global_word_783 v = global_word_782 v. Proof. apply global_sync_783. Qed.
Lemma wire_alias_784 v : global_word_784 v = global_word_783 v.
Proof. have E := global_closed_784_value v.
 change (Some (Gval (Fuint 1) (global_word_783 v)) = Some (Gval (Fuint 1) (global_word_784 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_785 v : global_word_785 v = global_word_784 v. Proof. apply global_sync_785. Qed.
Lemma wire_alias_787 v : global_word_787 v = global_word_39 v.
Proof. have E := global_closed_787_value v.
 change (Some (Gval (Fuint 1) (global_word_39 v)) = Some (Gval (Fuint 1) (global_word_787 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_788 v : global_word_788 v = global_word_787 v. Proof. apply global_sync_788. Qed.
Lemma wire_alias_789 v : global_word_789 v = global_word_788 v.
Proof. have E := global_closed_789_value v.
 change (Some (Gval (Fuint 1) (global_word_788 v)) = Some (Gval (Fuint 1) (global_word_789 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_790 v : global_word_790 v = global_word_789 v. Proof. apply global_sync_790. Qed.
Lemma wire_alias_792 v : global_word_792 v = global_word_40 v.
Proof. have E := global_closed_792_value v.
 change (Some (Gval (Fuint 1) (global_word_40 v)) = Some (Gval (Fuint 1) (global_word_792 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_793 v : global_word_793 v = global_word_792 v. Proof. apply global_sync_793. Qed.
Lemma wire_alias_794 v : global_word_794 v = global_word_793 v.
Proof. have E := global_closed_794_value v.
 change (Some (Gval (Fuint 1) (global_word_793 v)) = Some (Gval (Fuint 1) (global_word_794 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_795 v : global_word_795 v = global_word_794 v. Proof. apply global_sync_795. Qed.
Lemma wire_alias_803 v : global_word_803 v = global_word_802 v.
Proof. have E := global_closed_803_value v.
 change (Some (Gval (Fuint 2) (global_word_802 v)) = Some (Gval (Fuint 2) (global_word_803 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_805 v : global_word_805 v = global_word_804 v.
Proof. have E := global_closed_805_value v.
 change (Some (Gval (Fuint 1) (global_word_804 v)) = Some (Gval (Fuint 1) (global_word_805 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_806 v : global_word_806 v = global_word_805 v. Proof. apply global_sync_806. Qed.
Lemma wire_alias_807 v : global_word_807 v = global_word_806 v.
Proof. have E := global_closed_807_value v.
 change (Some (Gval (Fuint 1) (global_word_806 v)) = Some (Gval (Fuint 1) (global_word_807 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_808 v : global_word_808 v = global_word_807 v.
Proof. have E := global_closed_808_value v.
 change (Some (Gval (Fuint 1) (global_word_807 v)) = Some (Gval (Fuint 1) (global_word_808 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_809 v : global_word_809 v = global_word_808 v. Proof. apply global_sync_809. Qed.
Lemma wire_alias_811 v : global_word_811 v = global_word_42 v.
Proof. have E := global_closed_811_value v.
 change (Some (Gval (Fuint 1) (global_word_42 v)) = Some (Gval (Fuint 1) (global_word_811 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_812 v : global_word_812 v = global_word_811 v. Proof. apply global_sync_812. Qed.
Lemma wire_alias_813 v : global_word_813 v = global_word_812 v.
Proof. have E := global_closed_813_value v.
 change (Some (Gval (Fuint 1) (global_word_812 v)) = Some (Gval (Fuint 1) (global_word_813 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_814 v : global_word_814 v = global_word_813 v.
Proof. have E := global_closed_814_value v.
 change (Some (Gval (Fuint 1) (global_word_813 v)) = Some (Gval (Fuint 1) (global_word_814 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_815 v : global_word_815 v = global_word_814 v. Proof. apply global_sync_815. Qed.
Lemma wire_alias_823 v : global_word_823 v = global_word_822 v.
Proof. have E := global_closed_823_value v.
 change (Some (Gval (Fuint 2) (global_word_822 v)) = Some (Gval (Fuint 2) (global_word_823 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_825 v : global_word_825 v = global_word_824 v.
Proof. have E := global_closed_825_value v.
 change (Some (Gval (Fuint 1) (global_word_824 v)) = Some (Gval (Fuint 1) (global_word_825 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_826 v : global_word_826 v = global_word_825 v. Proof. apply global_sync_826. Qed.
Lemma wire_alias_827 v : global_word_827 v = global_word_826 v.
Proof. have E := global_closed_827_value v.
 change (Some (Gval (Fuint 1) (global_word_826 v)) = Some (Gval (Fuint 1) (global_word_827 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_828 v : global_word_828 v = global_word_827 v.
Proof. have E := global_closed_828_value v.
 change (Some (Gval (Fuint 1) (global_word_827 v)) = Some (Gval (Fuint 1) (global_word_828 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_829 v : global_word_829 v = global_word_828 v. Proof. apply global_sync_829. Qed.
Lemma wire_alias_832 v : global_word_832 v = global_word_831 v.
Proof. have E := global_closed_832_value v.
 change (Some (Gval (Fuint 1) (global_word_831 v)) = Some (Gval (Fuint 1) (global_word_832 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_833 v : global_word_833 v = global_word_832 v. Proof. apply global_sync_833. Qed.
Lemma wire_alias_834 v : global_word_834 v = global_word_833 v.
Proof. have E := global_closed_834_value v.
 change (Some (Gval (Fuint 1) (global_word_833 v)) = Some (Gval (Fuint 1) (global_word_834 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_835 v : global_word_835 v = global_word_834 v.
Proof. have E := global_closed_835_value v.
 change (Some (Gval (Fuint 1) (global_word_834 v)) = Some (Gval (Fuint 1) (global_word_835 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_836 v : global_word_836 v = global_word_835 v. Proof. apply global_sync_836. Qed.
Lemma wire_alias_839 v : global_word_839 v = global_word_838 v.
Proof. have E := global_closed_839_value v.
 change (Some (Gval (Fuint 1) (global_word_838 v)) = Some (Gval (Fuint 1) (global_word_839 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_840 v : global_word_840 v = global_word_839 v. Proof. apply global_sync_840. Qed.
Lemma wire_alias_841 v : global_word_841 v = global_word_840 v.
Proof. have E := global_closed_841_value v.
 change (Some (Gval (Fuint 1) (global_word_840 v)) = Some (Gval (Fuint 1) (global_word_841 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_842 v : global_word_842 v = global_word_841 v.
Proof. have E := global_closed_842_value v.
 change (Some (Gval (Fuint 1) (global_word_841 v)) = Some (Gval (Fuint 1) (global_word_842 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_843 v : global_word_843 v = global_word_842 v. Proof. apply global_sync_843. Qed.
Lemma wire_alias_845 v : global_word_845 v = global_word_837 v.
Proof. have E := global_closed_845_value v.
 change (Some (Gval (Fuint 1) (global_word_837 v)) = Some (Gval (Fuint 1) (global_word_845 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_846 v : global_word_846 v = global_word_845 v. Proof. apply global_sync_846. Qed.
Lemma wire_alias_847 v : global_word_847 v = global_word_846 v.
Proof. have E := global_closed_847_value v.
 change (Some (Gval (Fuint 1) (global_word_846 v)) = Some (Gval (Fuint 1) (global_word_847 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_848 v : global_word_848 v = global_word_847 v.
Proof. have E := global_closed_848_value v.
 change (Some (Gval (Fuint 1) (global_word_847 v)) = Some (Gval (Fuint 1) (global_word_848 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_849 v : global_word_849 v = global_word_848 v. Proof. apply global_sync_849. Qed.
Lemma wire_alias_851 v : global_word_851 v = global_word_45 v.
Proof. have E := global_closed_851_value v.
 change (Some (Gval (Fuint 1) (global_word_45 v)) = Some (Gval (Fuint 1) (global_word_851 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_852 v : global_word_852 v = global_word_851 v. Proof. apply global_sync_852. Qed.
Lemma wire_alias_853 v : global_word_853 v = global_word_852 v.
Proof. have E := global_closed_853_value v.
 change (Some (Gval (Fuint 1) (global_word_852 v)) = Some (Gval (Fuint 1) (global_word_853 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_854 v : global_word_854 v = global_word_853 v. Proof. apply global_sync_854. Qed.
Lemma wire_alias_856 v : global_word_856 v = global_word_43 v.
Proof. have E := global_closed_856_value v.
 change (Some (Gval (Fuint 1) (global_word_43 v)) = Some (Gval (Fuint 1) (global_word_856 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_857 v : global_word_857 v = global_word_856 v. Proof. apply global_sync_857. Qed.
Lemma wire_alias_858 v : global_word_858 v = global_word_857 v.
Proof. have E := global_closed_858_value v.
 change (Some (Gval (Fuint 1) (global_word_857 v)) = Some (Gval (Fuint 1) (global_word_858 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_859 v : global_word_859 v = global_word_858 v. Proof. apply global_sync_859. Qed.
Lemma wire_alias_861 v : global_word_861 v = global_word_44 v.
Proof. have E := global_closed_861_value v.
 change (Some (Gval (Fuint 1) (global_word_44 v)) = Some (Gval (Fuint 1) (global_word_861 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_862 v : global_word_862 v = global_word_861 v. Proof. apply global_sync_862. Qed.
Lemma wire_alias_863 v : global_word_863 v = global_word_862 v.
Proof. have E := global_closed_863_value v.
 change (Some (Gval (Fuint 1) (global_word_862 v)) = Some (Gval (Fuint 1) (global_word_863 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_864 v : global_word_864 v = global_word_863 v. Proof. apply global_sync_864. Qed.
Lemma wire_alias_872 v : global_word_872 v = global_word_871 v.
Proof. have E := global_closed_872_value v.
 change (Some (Gval (Fuint 2) (global_word_871 v)) = Some (Gval (Fuint 2) (global_word_872 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_874 v : global_word_874 v = global_word_873 v.
Proof. have E := global_closed_874_value v.
 change (Some (Gval (Fuint 1) (global_word_873 v)) = Some (Gval (Fuint 1) (global_word_874 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_875 v : global_word_875 v = global_word_874 v. Proof. apply global_sync_875. Qed.
Lemma wire_alias_876 v : global_word_876 v = global_word_875 v.
Proof. have E := global_closed_876_value v.
 change (Some (Gval (Fuint 1) (global_word_875 v)) = Some (Gval (Fuint 1) (global_word_876 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_877 v : global_word_877 v = global_word_876 v.
Proof. have E := global_closed_877_value v.
 change (Some (Gval (Fuint 1) (global_word_876 v)) = Some (Gval (Fuint 1) (global_word_877 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_878 v : global_word_878 v = global_word_877 v. Proof. apply global_sync_878. Qed.
Lemma wire_alias_880 v : global_word_880 v = global_word_46 v.
Proof. have E := global_closed_880_value v.
 change (Some (Gval (Fuint 1) (global_word_46 v)) = Some (Gval (Fuint 1) (global_word_880 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_881 v : global_word_881 v = global_word_880 v. Proof. apply global_sync_881. Qed.
Lemma wire_alias_882 v : global_word_882 v = global_word_881 v.
Proof. have E := global_closed_882_value v.
 change (Some (Gval (Fuint 1) (global_word_881 v)) = Some (Gval (Fuint 1) (global_word_882 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_883 v : global_word_883 v = global_word_882 v.
Proof. have E := global_closed_883_value v.
 change (Some (Gval (Fuint 1) (global_word_882 v)) = Some (Gval (Fuint 1) (global_word_883 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_884 v : global_word_884 v = global_word_883 v. Proof. apply global_sync_884. Qed.
Lemma wire_alias_892 v : global_word_892 v = global_word_891 v.
Proof. have E := global_closed_892_value v.
 change (Some (Gval (Fuint 2) (global_word_891 v)) = Some (Gval (Fuint 2) (global_word_892 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_894 v : global_word_894 v = global_word_893 v.
Proof. have E := global_closed_894_value v.
 change (Some (Gval (Fuint 1) (global_word_893 v)) = Some (Gval (Fuint 1) (global_word_894 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_895 v : global_word_895 v = global_word_894 v. Proof. apply global_sync_895. Qed.
Lemma wire_alias_896 v : global_word_896 v = global_word_895 v.
Proof. have E := global_closed_896_value v.
 change (Some (Gval (Fuint 1) (global_word_895 v)) = Some (Gval (Fuint 1) (global_word_896 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_897 v : global_word_897 v = global_word_896 v.
Proof. have E := global_closed_897_value v.
 change (Some (Gval (Fuint 1) (global_word_896 v)) = Some (Gval (Fuint 1) (global_word_897 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_898 v : global_word_898 v = global_word_897 v. Proof. apply global_sync_898. Qed.
Lemma wire_alias_901 v : global_word_901 v = global_word_900 v.
Proof. have E := global_closed_901_value v.
 change (Some (Gval (Fuint 1) (global_word_900 v)) = Some (Gval (Fuint 1) (global_word_901 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_902 v : global_word_902 v = global_word_901 v. Proof. apply global_sync_902. Qed.
Lemma wire_alias_903 v : global_word_903 v = global_word_902 v.
Proof. have E := global_closed_903_value v.
 change (Some (Gval (Fuint 1) (global_word_902 v)) = Some (Gval (Fuint 1) (global_word_903 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_904 v : global_word_904 v = global_word_903 v.
Proof. have E := global_closed_904_value v.
 change (Some (Gval (Fuint 1) (global_word_903 v)) = Some (Gval (Fuint 1) (global_word_904 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_905 v : global_word_905 v = global_word_904 v. Proof. apply global_sync_905. Qed.
Lemma wire_alias_908 v : global_word_908 v = global_word_907 v.
Proof. have E := global_closed_908_value v.
 change (Some (Gval (Fuint 1) (global_word_907 v)) = Some (Gval (Fuint 1) (global_word_908 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_909 v : global_word_909 v = global_word_908 v. Proof. apply global_sync_909. Qed.
Lemma wire_alias_910 v : global_word_910 v = global_word_909 v.
Proof. have E := global_closed_910_value v.
 change (Some (Gval (Fuint 1) (global_word_909 v)) = Some (Gval (Fuint 1) (global_word_910 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_911 v : global_word_911 v = global_word_910 v.
Proof. have E := global_closed_911_value v.
 change (Some (Gval (Fuint 1) (global_word_910 v)) = Some (Gval (Fuint 1) (global_word_911 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_912 v : global_word_912 v = global_word_911 v. Proof. apply global_sync_912. Qed.
Lemma wire_alias_914 v : global_word_914 v = global_word_49 v.
Proof. have E := global_closed_914_value v.
 change (Some (Gval (Fuint 1) (global_word_49 v)) = Some (Gval (Fuint 1) (global_word_914 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_915 v : global_word_915 v = global_word_914 v. Proof. apply global_sync_915. Qed.
Lemma wire_alias_917 v : global_word_917 v = global_word_47 v.
Proof. have E := global_closed_917_value v.
 change (Some (Gval (Fuint 1) (global_word_47 v)) = Some (Gval (Fuint 1) (global_word_917 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_918 v : global_word_918 v = global_word_917 v. Proof. apply global_sync_918. Qed.
Lemma wire_alias_920 v : global_word_920 v = global_word_48 v.
Proof. have E := global_closed_920_value v.
 change (Some (Gval (Fuint 1) (global_word_48 v)) = Some (Gval (Fuint 1) (global_word_920 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_921 v : global_word_921 v = global_word_920 v. Proof. apply global_sync_921. Qed.
Lemma wire_alias_929 v : global_word_929 v = global_word_928 v.
Proof. have E := global_closed_929_value v.
 change (Some (Gval (Fuint 2) (global_word_928 v)) = Some (Gval (Fuint 2) (global_word_929 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_931 v : global_word_931 v = global_word_930 v.
Proof. have E := global_closed_931_value v.
 change (Some (Gval (Fuint 1) (global_word_930 v)) = Some (Gval (Fuint 1) (global_word_931 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_932 v : global_word_932 v = global_word_931 v. Proof. apply global_sync_932. Qed.
Lemma wire_alias_935 v : global_word_935 v = global_word_934 v.
Proof. have E := global_closed_935_value v.
 change (Some (Gval (Fuint 1) (global_word_934 v)) = Some (Gval (Fuint 1) (global_word_935 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_936 v : global_word_936 v = global_word_935 v. Proof. apply global_sync_936. Qed.
Lemma wire_alias_938 v : global_word_938 v = global_word_50 v.
Proof. have E := global_closed_938_value v.
 change (Some (Gval (Fuint 1) (global_word_50 v)) = Some (Gval (Fuint 1) (global_word_938 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_939 v : global_word_939 v = global_word_938 v. Proof. apply global_sync_939. Qed.
Lemma wire_alias_941 v : global_word_941 v = global_word_51 v.
Proof. have E := global_closed_941_value v.
 change (Some (Gval (Fuint 1) (global_word_51 v)) = Some (Gval (Fuint 1) (global_word_941 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_942 v : global_word_942 v = global_word_941 v. Proof. apply global_sync_942. Qed.
Lemma wire_alias_947 v : global_word_947 v = global_word_946 v.
Proof. have E := global_closed_947_value v.
 change (Some (Gval (Fuint 2) (global_word_946 v)) = Some (Gval (Fuint 2) (global_word_947 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_949 v : global_word_949 v = global_word_948 v.
Proof. have E := global_closed_949_value v.
 change (Some (Gval (Fuint 1) (global_word_948 v)) = Some (Gval (Fuint 1) (global_word_949 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_950 v : global_word_950 v = global_word_949 v. Proof. apply global_sync_950. Qed.
Lemma wire_alias_953 v : global_word_953 v = global_word_952 v.
Proof. have E := global_closed_953_value v.
 change (Some (Gval (Fuint 1) (global_word_952 v)) = Some (Gval (Fuint 1) (global_word_953 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_954 v : global_word_954 v = global_word_953 v. Proof. apply global_sync_954. Qed.
Lemma wire_alias_956 v : global_word_956 v = global_word_52 v.
Proof. have E := global_closed_956_value v.
 change (Some (Gval (Fuint 1) (global_word_52 v)) = Some (Gval (Fuint 1) (global_word_956 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_957 v : global_word_957 v = global_word_956 v. Proof. apply global_sync_957. Qed.
Lemma wire_alias_959 v : global_word_959 v = global_word_54 v.
Proof. have E := global_closed_959_value v.
 change (Some (Gval (Fuint 1) (global_word_54 v)) = Some (Gval (Fuint 1) (global_word_959 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_960 v : global_word_960 v = global_word_959 v. Proof. apply global_sync_960. Qed.
Lemma wire_alias_965 v : global_word_965 v = global_word_964 v.
Proof. have E := global_closed_965_value v.
 change (Some (Gval (Fuint 2) (global_word_964 v)) = Some (Gval (Fuint 2) (global_word_965 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_967 v : global_word_967 v = global_word_966 v.
Proof. have E := global_closed_967_value v.
 change (Some (Gval (Fuint 1) (global_word_966 v)) = Some (Gval (Fuint 1) (global_word_967 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_968 v : global_word_968 v = global_word_967 v. Proof. apply global_sync_968. Qed.
Lemma wire_alias_971 v : global_word_971 v = global_word_970 v.
Proof. have E := global_closed_971_value v.
 change (Some (Gval (Fuint 1) (global_word_970 v)) = Some (Gval (Fuint 1) (global_word_971 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_972 v : global_word_972 v = global_word_971 v. Proof. apply global_sync_972. Qed.
Lemma wire_alias_974 v : global_word_974 v = global_word_309 v.
Proof. have E := global_closed_974_value v.
 change (Some (Gval (Fuint 1) (global_word_309 v)) = Some (Gval (Fuint 1) (global_word_974 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_975 v : global_word_975 v = global_word_974 v. Proof. apply global_sync_975. Qed.
Lemma wire_alias_977 v : global_word_977 v = global_word_295 v.
Proof. have E := global_closed_977_value v.
 change (Some (Gval (Fuint 1) (global_word_295 v)) = Some (Gval (Fuint 1) (global_word_977 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_978 v : global_word_978 v = global_word_977 v. Proof. apply global_sync_978. Qed.
Lemma wire_alias_983 v : global_word_983 v = global_word_982 v.
Proof. have E := global_closed_983_value v.
 change (Some (Gval (Fuint 2) (global_word_982 v)) = Some (Gval (Fuint 2) (global_word_983 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_985 v : global_word_985 v = global_word_984 v.
Proof. have E := global_closed_985_value v.
 change (Some (Gval (Fuint 1) (global_word_984 v)) = Some (Gval (Fuint 1) (global_word_985 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_986 v : global_word_986 v = global_word_985 v. Proof. apply global_sync_986. Qed.
Lemma wire_alias_989 v : global_word_989 v = global_word_988 v.
Proof. have E := global_closed_989_value v.
 change (Some (Gval (Fuint 1) (global_word_988 v)) = Some (Gval (Fuint 1) (global_word_989 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_990 v : global_word_990 v = global_word_989 v. Proof. apply global_sync_990. Qed.
Lemma wire_alias_992 v : global_word_992 v = global_word_333 v.
Proof. have E := global_closed_992_value v.
 change (Some (Gval (Fuint 1) (global_word_333 v)) = Some (Gval (Fuint 1) (global_word_992 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_993 v : global_word_993 v = global_word_992 v. Proof. apply global_sync_993. Qed.
Lemma wire_alias_995 v : global_word_995 v = global_word_313 v.
Proof. have E := global_closed_995_value v.
 change (Some (Gval (Fuint 1) (global_word_313 v)) = Some (Gval (Fuint 1) (global_word_995 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_996 v : global_word_996 v = global_word_995 v. Proof. apply global_sync_996. Qed.
Lemma wire_alias_1001 v : global_word_1001 v = global_word_1000 v.
Proof. have E := global_closed_1001_value v.
 change (Some (Gval (Fuint 2) (global_word_1000 v)) = Some (Gval (Fuint 2) (global_word_1001 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1003 v : global_word_1003 v = global_word_1002 v.
Proof. have E := global_closed_1003_value v.
 change (Some (Gval (Fuint 1) (global_word_1002 v)) = Some (Gval (Fuint 1) (global_word_1003 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1004 v : global_word_1004 v = global_word_1003 v. Proof. apply global_sync_1004. Qed.
Lemma wire_alias_1007 v : global_word_1007 v = global_word_1006 v.
Proof. have E := global_closed_1007_value v.
 change (Some (Gval (Fuint 1) (global_word_1006 v)) = Some (Gval (Fuint 1) (global_word_1007 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1008 v : global_word_1008 v = global_word_1007 v. Proof. apply global_sync_1008. Qed.
Lemma wire_alias_1010 v : global_word_1010 v = global_word_357 v.
Proof. have E := global_closed_1010_value v.
 change (Some (Gval (Fuint 1) (global_word_357 v)) = Some (Gval (Fuint 1) (global_word_1010 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1011 v : global_word_1011 v = global_word_1010 v. Proof. apply global_sync_1011. Qed.
Lemma wire_alias_1013 v : global_word_1013 v = global_word_337 v.
Proof. have E := global_closed_1013_value v.
 change (Some (Gval (Fuint 1) (global_word_337 v)) = Some (Gval (Fuint 1) (global_word_1013 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1014 v : global_word_1014 v = global_word_1013 v. Proof. apply global_sync_1014. Qed.
Lemma wire_alias_1019 v : global_word_1019 v = global_word_1018 v.
Proof. have E := global_closed_1019_value v.
 change (Some (Gval (Fuint 2) (global_word_1018 v)) = Some (Gval (Fuint 2) (global_word_1019 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1021 v : global_word_1021 v = global_word_1020 v.
Proof. have E := global_closed_1021_value v.
 change (Some (Gval (Fuint 1) (global_word_1020 v)) = Some (Gval (Fuint 1) (global_word_1021 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1022 v : global_word_1022 v = global_word_1021 v. Proof. apply global_sync_1022. Qed.
Lemma wire_alias_1025 v : global_word_1025 v = global_word_1024 v.
Proof. have E := global_closed_1025_value v.
 change (Some (Gval (Fuint 1) (global_word_1024 v)) = Some (Gval (Fuint 1) (global_word_1025 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1026 v : global_word_1026 v = global_word_1025 v. Proof. apply global_sync_1026. Qed.
Lemma wire_alias_1028 v : global_word_1028 v = global_word_416 v.
Proof. have E := global_closed_1028_value v.
 change (Some (Gval (Fuint 1) (global_word_416 v)) = Some (Gval (Fuint 1) (global_word_1028 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1029 v : global_word_1029 v = global_word_1028 v. Proof. apply global_sync_1029. Qed.
Lemma wire_alias_1031 v : global_word_1031 v = global_word_361 v.
Proof. have E := global_closed_1031_value v.
 change (Some (Gval (Fuint 1) (global_word_361 v)) = Some (Gval (Fuint 1) (global_word_1031 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1032 v : global_word_1032 v = global_word_1031 v. Proof. apply global_sync_1032. Qed.
Lemma wire_alias_1037 v : global_word_1037 v = global_word_1036 v.
Proof. have E := global_closed_1037_value v.
 change (Some (Gval (Fuint 2) (global_word_1036 v)) = Some (Gval (Fuint 2) (global_word_1037 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1039 v : global_word_1039 v = global_word_1038 v.
Proof. have E := global_closed_1039_value v.
 change (Some (Gval (Fuint 1) (global_word_1038 v)) = Some (Gval (Fuint 1) (global_word_1039 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1040 v : global_word_1040 v = global_word_1039 v. Proof. apply global_sync_1040. Qed.
Lemma wire_alias_1043 v : global_word_1043 v = global_word_1042 v.
Proof. have E := global_closed_1043_value v.
 change (Some (Gval (Fuint 1) (global_word_1042 v)) = Some (Gval (Fuint 1) (global_word_1043 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1044 v : global_word_1044 v = global_word_1043 v. Proof. apply global_sync_1044. Qed.
Lemma wire_alias_1046 v : global_word_1046 v = global_word_485 v.
Proof. have E := global_closed_1046_value v.
 change (Some (Gval (Fuint 1) (global_word_485 v)) = Some (Gval (Fuint 1) (global_word_1046 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1047 v : global_word_1047 v = global_word_1046 v. Proof. apply global_sync_1047. Qed.
Lemma wire_alias_1049 v : global_word_1049 v = global_word_430 v.
Proof. have E := global_closed_1049_value v.
 change (Some (Gval (Fuint 1) (global_word_430 v)) = Some (Gval (Fuint 1) (global_word_1049 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1050 v : global_word_1050 v = global_word_1049 v. Proof. apply global_sync_1050. Qed.
Lemma wire_alias_1055 v : global_word_1055 v = global_word_1054 v.
Proof. have E := global_closed_1055_value v.
 change (Some (Gval (Fuint 2) (global_word_1054 v)) = Some (Gval (Fuint 2) (global_word_1055 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1057 v : global_word_1057 v = global_word_1056 v.
Proof. have E := global_closed_1057_value v.
 change (Some (Gval (Fuint 1) (global_word_1056 v)) = Some (Gval (Fuint 1) (global_word_1057 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1058 v : global_word_1058 v = global_word_1057 v. Proof. apply global_sync_1058. Qed.
Lemma wire_alias_1061 v : global_word_1061 v = global_word_1060 v.
Proof. have E := global_closed_1061_value v.
 change (Some (Gval (Fuint 1) (global_word_1060 v)) = Some (Gval (Fuint 1) (global_word_1061 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1062 v : global_word_1062 v = global_word_1061 v. Proof. apply global_sync_1062. Qed.
Lemma wire_alias_1064 v : global_word_1064 v = global_word_499 v.
Proof. have E := global_closed_1064_value v.
 change (Some (Gval (Fuint 1) (global_word_499 v)) = Some (Gval (Fuint 1) (global_word_1064 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1065 v : global_word_1065 v = global_word_1064 v. Proof. apply global_sync_1065. Qed.
Lemma wire_alias_1067 v : global_word_1067 v = global_word_554 v.
Proof. have E := global_closed_1067_value v.
 change (Some (Gval (Fuint 1) (global_word_554 v)) = Some (Gval (Fuint 1) (global_word_1067 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1068 v : global_word_1068 v = global_word_1067 v. Proof. apply global_sync_1068. Qed.
Lemma wire_alias_1070 v : global_word_1070 v = global_word_25 v.
Proof. have E := global_closed_1070_value v.
 change (Some (Gval (Fuint 1) (global_word_25 v)) = Some (Gval (Fuint 1) (global_word_1070 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1071 v : global_word_1071 v = global_word_1070 v. Proof. apply global_sync_1071. Qed.
Lemma wire_alias_1079 v : global_word_1079 v = global_word_1078 v.
Proof. have E := global_closed_1079_value v.
 change (Some (Gval (Fuint 2) (global_word_1078 v)) = Some (Gval (Fuint 2) (global_word_1079 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1081 v : global_word_1081 v = global_word_1080 v.
Proof. have E := global_closed_1081_value v.
 change (Some (Gval (Fuint 1) (global_word_1080 v)) = Some (Gval (Fuint 1) (global_word_1081 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1082 v : global_word_1082 v = global_word_1081 v. Proof. apply global_sync_1082. Qed.
Lemma wire_alias_1085 v : global_word_1085 v = global_word_1084 v.
Proof. have E := global_closed_1085_value v.
 change (Some (Gval (Fuint 1) (global_word_1084 v)) = Some (Gval (Fuint 1) (global_word_1085 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1086 v : global_word_1086 v = global_word_1085 v. Proof. apply global_sync_1086. Qed.
Lemma wire_alias_1088 v : global_word_1088 v = global_word_568 v.
Proof. have E := global_closed_1088_value v.
 change (Some (Gval (Fuint 1) (global_word_568 v)) = Some (Gval (Fuint 1) (global_word_1088 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1089 v : global_word_1089 v = global_word_1088 v. Proof. apply global_sync_1089. Qed.
Lemma wire_alias_1091 v : global_word_1091 v = global_word_623 v.
Proof. have E := global_closed_1091_value v.
 change (Some (Gval (Fuint 1) (global_word_623 v)) = Some (Gval (Fuint 1) (global_word_1091 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1092 v : global_word_1092 v = global_word_1091 v. Proof. apply global_sync_1092. Qed.
Lemma wire_alias_1094 v : global_word_1094 v = global_word_30 v.
Proof. have E := global_closed_1094_value v.
 change (Some (Gval (Fuint 1) (global_word_30 v)) = Some (Gval (Fuint 1) (global_word_1094 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1095 v : global_word_1095 v = global_word_1094 v. Proof. apply global_sync_1095. Qed.
Lemma wire_alias_1103 v : global_word_1103 v = global_word_1102 v.
Proof. have E := global_closed_1103_value v.
 change (Some (Gval (Fuint 2) (global_word_1102 v)) = Some (Gval (Fuint 2) (global_word_1103 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1105 v : global_word_1105 v = global_word_1104 v.
Proof. have E := global_closed_1105_value v.
 change (Some (Gval (Fuint 1) (global_word_1104 v)) = Some (Gval (Fuint 1) (global_word_1105 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1106 v : global_word_1106 v = global_word_1105 v. Proof. apply global_sync_1106. Qed.
Lemma wire_alias_1109 v : global_word_1109 v = global_word_1108 v.
Proof. have E := global_closed_1109_value v.
 change (Some (Gval (Fuint 1) (global_word_1108 v)) = Some (Gval (Fuint 1) (global_word_1109 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1110 v : global_word_1110 v = global_word_1109 v. Proof. apply global_sync_1110. Qed.
Lemma wire_alias_1112 v : global_word_1112 v = global_word_692 v.
Proof. have E := global_closed_1112_value v.
 change (Some (Gval (Fuint 1) (global_word_692 v)) = Some (Gval (Fuint 1) (global_word_1112 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1113 v : global_word_1113 v = global_word_1112 v. Proof. apply global_sync_1113. Qed.
Lemma wire_alias_1115 v : global_word_1115 v = global_word_637 v.
Proof. have E := global_closed_1115_value v.
 change (Some (Gval (Fuint 1) (global_word_637 v)) = Some (Gval (Fuint 1) (global_word_1115 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1116 v : global_word_1116 v = global_word_1115 v. Proof. apply global_sync_1116. Qed.
Lemma wire_alias_1121 v : global_word_1121 v = global_word_1120 v.
Proof. have E := global_closed_1121_value v.
 change (Some (Gval (Fuint 2) (global_word_1120 v)) = Some (Gval (Fuint 2) (global_word_1121 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1123 v : global_word_1123 v = global_word_1122 v.
Proof. have E := global_closed_1123_value v.
 change (Some (Gval (Fuint 1) (global_word_1122 v)) = Some (Gval (Fuint 1) (global_word_1123 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1124 v : global_word_1124 v = global_word_1123 v. Proof. apply global_sync_1124. Qed.
Lemma wire_alias_1127 v : global_word_1127 v = global_word_1126 v.
Proof. have E := global_closed_1127_value v.
 change (Some (Gval (Fuint 1) (global_word_1126 v)) = Some (Gval (Fuint 1) (global_word_1127 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1128 v : global_word_1128 v = global_word_1127 v. Proof. apply global_sync_1128. Qed.
Lemma wire_alias_1130 v : global_word_1130 v = global_word_761 v.
Proof. have E := global_closed_1130_value v.
 change (Some (Gval (Fuint 1) (global_word_761 v)) = Some (Gval (Fuint 1) (global_word_1130 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1131 v : global_word_1131 v = global_word_1130 v. Proof. apply global_sync_1131. Qed.
Lemma wire_alias_1133 v : global_word_1133 v = global_word_706 v.
Proof. have E := global_closed_1133_value v.
 change (Some (Gval (Fuint 1) (global_word_706 v)) = Some (Gval (Fuint 1) (global_word_1133 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1134 v : global_word_1134 v = global_word_1133 v. Proof. apply global_sync_1134. Qed.
Lemma wire_alias_1139 v : global_word_1139 v = global_word_1138 v.
Proof. have E := global_closed_1139_value v.
 change (Some (Gval (Fuint 2) (global_word_1138 v)) = Some (Gval (Fuint 2) (global_word_1139 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1141 v : global_word_1141 v = global_word_1140 v.
Proof. have E := global_closed_1141_value v.
 change (Some (Gval (Fuint 1) (global_word_1140 v)) = Some (Gval (Fuint 1) (global_word_1141 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1142 v : global_word_1142 v = global_word_1141 v. Proof. apply global_sync_1142. Qed.
Lemma wire_alias_1145 v : global_word_1145 v = global_word_1144 v.
Proof. have E := global_closed_1145_value v.
 change (Some (Gval (Fuint 1) (global_word_1144 v)) = Some (Gval (Fuint 1) (global_word_1145 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1146 v : global_word_1146 v = global_word_1145 v. Proof. apply global_sync_1146. Qed.
Lemma wire_alias_1148 v : global_word_1148 v = global_word_830 v.
Proof. have E := global_closed_1148_value v.
 change (Some (Gval (Fuint 1) (global_word_830 v)) = Some (Gval (Fuint 1) (global_word_1148 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1149 v : global_word_1149 v = global_word_1148 v. Proof. apply global_sync_1149. Qed.
Lemma wire_alias_1151 v : global_word_1151 v = global_word_775 v.
Proof. have E := global_closed_1151_value v.
 change (Some (Gval (Fuint 1) (global_word_775 v)) = Some (Gval (Fuint 1) (global_word_1151 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1152 v : global_word_1152 v = global_word_1151 v. Proof. apply global_sync_1152. Qed.
Lemma wire_alias_1157 v : global_word_1157 v = global_word_1156 v.
Proof. have E := global_closed_1157_value v.
 change (Some (Gval (Fuint 2) (global_word_1156 v)) = Some (Gval (Fuint 2) (global_word_1157 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1159 v : global_word_1159 v = global_word_1158 v.
Proof. have E := global_closed_1159_value v.
 change (Some (Gval (Fuint 1) (global_word_1158 v)) = Some (Gval (Fuint 1) (global_word_1159 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1160 v : global_word_1160 v = global_word_1159 v. Proof. apply global_sync_1160. Qed.
Lemma wire_alias_1163 v : global_word_1163 v = global_word_1162 v.
Proof. have E := global_closed_1163_value v.
 change (Some (Gval (Fuint 1) (global_word_1162 v)) = Some (Gval (Fuint 1) (global_word_1163 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1164 v : global_word_1164 v = global_word_1163 v. Proof. apply global_sync_1164. Qed.
Lemma wire_alias_1166 v : global_word_1166 v = global_word_899 v.
Proof. have E := global_closed_1166_value v.
 change (Some (Gval (Fuint 1) (global_word_899 v)) = Some (Gval (Fuint 1) (global_word_1166 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1167 v : global_word_1167 v = global_word_1166 v. Proof. apply global_sync_1167. Qed.
Lemma wire_alias_1169 v : global_word_1169 v = global_word_844 v.
Proof. have E := global_closed_1169_value v.
 change (Some (Gval (Fuint 1) (global_word_844 v)) = Some (Gval (Fuint 1) (global_word_1169 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1170 v : global_word_1170 v = global_word_1169 v. Proof. apply global_sync_1170. Qed.
Lemma wire_alias_1175 v : global_word_1175 v = global_word_1174 v.
Proof. have E := global_closed_1175_value v.
 change (Some (Gval (Fuint 2) (global_word_1174 v)) = Some (Gval (Fuint 2) (global_word_1175 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1177 v : global_word_1177 v = global_word_1176 v.
Proof. have E := global_closed_1177_value v.
 change (Some (Gval (Fuint 1) (global_word_1176 v)) = Some (Gval (Fuint 1) (global_word_1177 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1178 v : global_word_1178 v = global_word_1177 v. Proof. apply global_sync_1178. Qed.
Lemma wire_alias_1181 v : global_word_1181 v = global_word_1180 v.
Proof. have E := global_closed_1181_value v.
 change (Some (Gval (Fuint 1) (global_word_1180 v)) = Some (Gval (Fuint 1) (global_word_1181 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1182 v : global_word_1182 v = global_word_1181 v. Proof. apply global_sync_1182. Qed.
Lemma wire_alias_1184 v : global_word_1184 v = global_word_913 v.
Proof. have E := global_closed_1184_value v.
 change (Some (Gval (Fuint 1) (global_word_913 v)) = Some (Gval (Fuint 1) (global_word_1184 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1185 v : global_word_1185 v = global_word_1184 v. Proof. apply global_sync_1185. Qed.
Lemma wire_alias_1187 v : global_word_1187 v = global_word_933 v.
Proof. have E := global_closed_1187_value v.
 change (Some (Gval (Fuint 1) (global_word_933 v)) = Some (Gval (Fuint 1) (global_word_1187 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1188 v : global_word_1188 v = global_word_1187 v. Proof. apply global_sync_1188. Qed.
Lemma wire_alias_1190 v : global_word_1190 v = global_word_906 v.
Proof. have E := global_closed_1190_value v.
 change (Some (Gval (Fuint 1) (global_word_906 v)) = Some (Gval (Fuint 1) (global_word_1190 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1191 v : global_word_1191 v = global_word_1190 v. Proof. apply global_sync_1191. Qed.
Lemma wire_alias_1199 v : global_word_1199 v = global_word_1198 v.
Proof. have E := global_closed_1199_value v.
 change (Some (Gval (Fuint 2) (global_word_1198 v)) = Some (Gval (Fuint 2) (global_word_1199 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1201 v : global_word_1201 v = global_word_1200 v.
Proof. have E := global_closed_1201_value v.
 change (Some (Gval (Fuint 1) (global_word_1200 v)) = Some (Gval (Fuint 1) (global_word_1201 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1202 v : global_word_1202 v = global_word_1201 v. Proof. apply global_sync_1202. Qed.
Lemma wire_alias_1205 v : global_word_1205 v = global_word_1204 v.
Proof. have E := global_closed_1205_value v.
 change (Some (Gval (Fuint 1) (global_word_1204 v)) = Some (Gval (Fuint 1) (global_word_1205 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1206 v : global_word_1206 v = global_word_1205 v. Proof. apply global_sync_1206. Qed.
Lemma wire_alias_1208 v : global_word_1208 v = global_word_951 v.
Proof. have E := global_closed_1208_value v.
 change (Some (Gval (Fuint 1) (global_word_951 v)) = Some (Gval (Fuint 1) (global_word_1208 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1209 v : global_word_1209 v = global_word_1208 v. Proof. apply global_sync_1209. Qed.
Lemma wire_alias_1211 v : global_word_1211 v = global_word_937 v.
Proof. have E := global_closed_1211_value v.
 change (Some (Gval (Fuint 1) (global_word_937 v)) = Some (Gval (Fuint 1) (global_word_1211 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1212 v : global_word_1212 v = global_word_1211 v. Proof. apply global_sync_1212. Qed.
Lemma wire_alias_1217 v : global_word_1217 v = global_word_1216 v.
Proof. have E := global_closed_1217_value v.
 change (Some (Gval (Fuint 2) (global_word_1216 v)) = Some (Gval (Fuint 2) (global_word_1217 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1219 v : global_word_1219 v = global_word_1218 v.
Proof. have E := global_closed_1219_value v.
 change (Some (Gval (Fuint 1) (global_word_1218 v)) = Some (Gval (Fuint 1) (global_word_1219 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1220 v : global_word_1220 v = global_word_1219 v. Proof. apply global_sync_1220. Qed.
Lemma wire_alias_1223 v : global_word_1223 v = global_word_1222 v.
Proof. have E := global_closed_1223_value v.
 change (Some (Gval (Fuint 1) (global_word_1222 v)) = Some (Gval (Fuint 1) (global_word_1223 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1224 v : global_word_1224 v = global_word_1223 v. Proof. apply global_sync_1224. Qed.
Lemma wire_alias_1226 v : global_word_1226 v = global_word_969 v.
Proof. have E := global_closed_1226_value v.
 change (Some (Gval (Fuint 1) (global_word_969 v)) = Some (Gval (Fuint 1) (global_word_1226 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1227 v : global_word_1227 v = global_word_1226 v. Proof. apply global_sync_1227. Qed.
Lemma wire_alias_1229 v : global_word_1229 v = global_word_955 v.
Proof. have E := global_closed_1229_value v.
 change (Some (Gval (Fuint 1) (global_word_955 v)) = Some (Gval (Fuint 1) (global_word_1229 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1230 v : global_word_1230 v = global_word_1229 v. Proof. apply global_sync_1230. Qed.
Lemma wire_alias_1235 v : global_word_1235 v = global_word_1234 v.
Proof. have E := global_closed_1235_value v.
 change (Some (Gval (Fuint 2) (global_word_1234 v)) = Some (Gval (Fuint 2) (global_word_1235 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1237 v : global_word_1237 v = global_word_1236 v.
Proof. have E := global_closed_1237_value v.
 change (Some (Gval (Fuint 1) (global_word_1236 v)) = Some (Gval (Fuint 1) (global_word_1237 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1238 v : global_word_1238 v = global_word_1237 v. Proof. apply global_sync_1238. Qed.
Lemma wire_alias_1241 v : global_word_1241 v = global_word_1240 v.
Proof. have E := global_closed_1241_value v.
 change (Some (Gval (Fuint 1) (global_word_1240 v)) = Some (Gval (Fuint 1) (global_word_1241 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1242 v : global_word_1242 v = global_word_1241 v. Proof. apply global_sync_1242. Qed.
Lemma wire_alias_1244 v : global_word_1244 v = global_word_55 v.
Proof. have E := global_closed_1244_value v.
 change (Some (Gval (Fuint 1) (global_word_55 v)) = Some (Gval (Fuint 1) (global_word_1244 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1245 v : global_word_1245 v = global_word_1244 v. Proof. apply global_sync_1245. Qed.
Lemma wire_alias_1247 v : global_word_1247 v = global_word_973 v.
Proof. have E := global_closed_1247_value v.
 change (Some (Gval (Fuint 1) (global_word_973 v)) = Some (Gval (Fuint 1) (global_word_1247 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1248 v : global_word_1248 v = global_word_1247 v. Proof. apply global_sync_1248. Qed.
Lemma wire_alias_1253 v : global_word_1253 v = global_word_1252 v.
Proof. have E := global_closed_1253_value v.
 change (Some (Gval (Fuint 2) (global_word_1252 v)) = Some (Gval (Fuint 2) (global_word_1253 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1255 v : global_word_1255 v = global_word_1254 v.
Proof. have E := global_closed_1255_value v.
 change (Some (Gval (Fuint 1) (global_word_1254 v)) = Some (Gval (Fuint 1) (global_word_1255 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1256 v : global_word_1256 v = global_word_1255 v. Proof. apply global_sync_1256. Qed.
Lemma wire_alias_1259 v : global_word_1259 v = global_word_1258 v.
Proof. have E := global_closed_1259_value v.
 change (Some (Gval (Fuint 1) (global_word_1258 v)) = Some (Gval (Fuint 1) (global_word_1259 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1260 v : global_word_1260 v = global_word_1259 v. Proof. apply global_sync_1260. Qed.
Lemma wire_alias_1299 v : global_word_1299 v = global_word_1292 v.
Proof. have E := global_closed_1299_value v.
 change (Some (Gval (Fuint 16) (global_word_1292 v)) = Some (Gval (Fuint 16) (global_word_1299 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1310 v : global_word_1310 v = global_word_0 v.
Proof. have E := global_closed_1310_value v.
 change (Some (Gval Fclock (global_word_0 v)) = Some (Gval Fclock (global_word_1310 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1311 v : global_word_1311 v = global_word_1 v.
Proof. have E := global_closed_1311_value v.
 change (Some (Gval (Fuint 1) (global_word_1 v)) = Some (Gval (Fuint 1) (global_word_1311 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1312 v : global_word_1312 v = global_word_0 v.
Proof. have E := global_closed_1312_value v.
 change (Some (Gval Fclock (global_word_0 v)) = Some (Gval Fclock (global_word_1312 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1313 v : global_word_1313 v = global_word_1 v.
Proof. have E := global_closed_1313_value v.
 change (Some (Gval (Fuint 1) (global_word_1 v)) = Some (Gval (Fuint 1) (global_word_1313 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1314 v : global_word_1314 v = global_word_0 v.
Proof. have E := global_closed_1314_value v.
 change (Some (Gval Fclock (global_word_0 v)) = Some (Gval Fclock (global_word_1314 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1315 v : global_word_1315 v = global_word_1 v.
Proof. have E := global_closed_1315_value v.
 change (Some (Gval (Fuint 1) (global_word_1 v)) = Some (Gval (Fuint 1) (global_word_1315 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1316 v : global_word_1316 v = global_word_0 v.
Proof. have E := global_closed_1316_value v.
 change (Some (Gval Fclock (global_word_0 v)) = Some (Gval Fclock (global_word_1316 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1317 v : global_word_1317 v = global_word_1 v.
Proof. have E := global_closed_1317_value v.
 change (Some (Gval (Fuint 1) (global_word_1 v)) = Some (Gval (Fuint 1) (global_word_1317 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1318 v : global_word_1318 v = global_word_0 v.
Proof. have E := global_closed_1318_value v.
 change (Some (Gval Fclock (global_word_0 v)) = Some (Gval Fclock (global_word_1318 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1319 v : global_word_1319 v = global_word_1 v.
Proof. have E := global_closed_1319_value v.
 change (Some (Gval (Fuint 1) (global_word_1 v)) = Some (Gval (Fuint 1) (global_word_1319 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1320 v : global_word_1320 v = global_word_0 v.
Proof. have E := global_closed_1320_value v.
 change (Some (Gval Fclock (global_word_0 v)) = Some (Gval Fclock (global_word_1320 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1321 v : global_word_1321 v = global_word_1 v.
Proof. have E := global_closed_1321_value v.
 change (Some (Gval (Fuint 1) (global_word_1 v)) = Some (Gval (Fuint 1) (global_word_1321 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1322 v : global_word_1322 v = global_word_0 v.
Proof. have E := global_closed_1322_value v.
 change (Some (Gval Fclock (global_word_0 v)) = Some (Gval Fclock (global_word_1322 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1323 v : global_word_1323 v = global_word_1 v.
Proof. have E := global_closed_1323_value v.
 change (Some (Gval (Fuint 1) (global_word_1 v)) = Some (Gval (Fuint 1) (global_word_1323 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1324 v : global_word_1324 v = global_word_0 v.
Proof. have E := global_closed_1324_value v.
 change (Some (Gval Fclock (global_word_0 v)) = Some (Gval Fclock (global_word_1324 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1325 v : global_word_1325 v = global_word_1 v.
Proof. have E := global_closed_1325_value v.
 change (Some (Gval (Fuint 1) (global_word_1 v)) = Some (Gval (Fuint 1) (global_word_1325 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1326 v : global_word_1326 v = global_word_0 v.
Proof. have E := global_closed_1326_value v.
 change (Some (Gval Fclock (global_word_0 v)) = Some (Gval Fclock (global_word_1326 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1327 v : global_word_1327 v = global_word_1 v.
Proof. have E := global_closed_1327_value v.
 change (Some (Gval (Fuint 1) (global_word_1 v)) = Some (Gval (Fuint 1) (global_word_1327 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1328 v : global_word_1328 v = global_word_0 v.
Proof. have E := global_closed_1328_value v.
 change (Some (Gval Fclock (global_word_0 v)) = Some (Gval Fclock (global_word_1328 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1329 v : global_word_1329 v = global_word_1 v.
Proof. have E := global_closed_1329_value v.
 change (Some (Gval (Fuint 1) (global_word_1 v)) = Some (Gval (Fuint 1) (global_word_1329 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1330 v : global_word_1330 v = global_word_0 v.
Proof. have E := global_closed_1330_value v.
 change (Some (Gval Fclock (global_word_0 v)) = Some (Gval Fclock (global_word_1330 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1331 v : global_word_1331 v = global_word_1 v.
Proof. have E := global_closed_1331_value v.
 change (Some (Gval (Fuint 1) (global_word_1 v)) = Some (Gval (Fuint 1) (global_word_1331 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1332 v : global_word_1332 v = global_word_0 v.
Proof. have E := global_closed_1332_value v.
 change (Some (Gval Fclock (global_word_0 v)) = Some (Gval Fclock (global_word_1332 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1333 v : global_word_1333 v = global_word_1 v.
Proof. have E := global_closed_1333_value v.
 change (Some (Gval (Fuint 1) (global_word_1 v)) = Some (Gval (Fuint 1) (global_word_1333 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1334 v : global_word_1334 v = global_word_0 v.
Proof. have E := global_closed_1334_value v.
 change (Some (Gval Fclock (global_word_0 v)) = Some (Gval Fclock (global_word_1334 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1335 v : global_word_1335 v = global_word_1 v.
Proof. have E := global_closed_1335_value v.
 change (Some (Gval (Fuint 1) (global_word_1 v)) = Some (Gval (Fuint 1) (global_word_1335 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1336 v : global_word_1336 v = global_word_0 v.
Proof. have E := global_closed_1336_value v.
 change (Some (Gval Fclock (global_word_0 v)) = Some (Gval Fclock (global_word_1336 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1337 v : global_word_1337 v = global_word_1 v.
Proof. have E := global_closed_1337_value v.
 change (Some (Gval (Fuint 1) (global_word_1 v)) = Some (Gval (Fuint 1) (global_word_1337 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1338 v : global_word_1338 v = global_word_0 v.
Proof. have E := global_closed_1338_value v.
 change (Some (Gval Fclock (global_word_0 v)) = Some (Gval Fclock (global_word_1338 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1339 v : global_word_1339 v = global_word_1 v.
Proof. have E := global_closed_1339_value v.
 change (Some (Gval (Fuint 1) (global_word_1 v)) = Some (Gval (Fuint 1) (global_word_1339 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1340 v : global_word_1340 v = global_word_0 v.
Proof. have E := global_closed_1340_value v.
 change (Some (Gval Fclock (global_word_0 v)) = Some (Gval Fclock (global_word_1340 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1341 v : global_word_1341 v = global_word_1 v.
Proof. have E := global_closed_1341_value v.
 change (Some (Gval (Fuint 1) (global_word_1 v)) = Some (Gval (Fuint 1) (global_word_1341 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1342 v : global_word_1342 v = global_word_0 v.
Proof. have E := global_closed_1342_value v.
 change (Some (Gval Fclock (global_word_0 v)) = Some (Gval Fclock (global_word_1342 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1343 v : global_word_1343 v = global_word_1 v.
Proof. have E := global_closed_1343_value v.
 change (Some (Gval (Fuint 1) (global_word_1 v)) = Some (Gval (Fuint 1) (global_word_1343 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1344 v : global_word_1344 v = global_word_0 v.
Proof. have E := global_closed_1344_value v.
 change (Some (Gval Fclock (global_word_0 v)) = Some (Gval Fclock (global_word_1344 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1345 v : global_word_1345 v = global_word_1 v.
Proof. have E := global_closed_1345_value v.
 change (Some (Gval (Fuint 1) (global_word_1 v)) = Some (Gval (Fuint 1) (global_word_1345 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1346 v : global_word_1346 v = global_word_0 v.
Proof. have E := global_closed_1346_value v.
 change (Some (Gval Fclock (global_word_0 v)) = Some (Gval Fclock (global_word_1346 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1347 v : global_word_1347 v = global_word_1 v.
Proof. have E := global_closed_1347_value v.
 change (Some (Gval (Fuint 1) (global_word_1 v)) = Some (Gval (Fuint 1) (global_word_1347 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1348 v : global_word_1348 v = global_word_0 v.
Proof. have E := global_closed_1348_value v.
 change (Some (Gval Fclock (global_word_0 v)) = Some (Gval Fclock (global_word_1348 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1349 v : global_word_1349 v = global_word_1 v.
Proof. have E := global_closed_1349_value v.
 change (Some (Gval (Fuint 1) (global_word_1 v)) = Some (Gval (Fuint 1) (global_word_1349 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1350 v : global_word_1350 v = global_word_0 v.
Proof. have E := global_closed_1350_value v.
 change (Some (Gval Fclock (global_word_0 v)) = Some (Gval Fclock (global_word_1350 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1351 v : global_word_1351 v = global_word_1 v.
Proof. have E := global_closed_1351_value v.
 change (Some (Gval (Fuint 1) (global_word_1 v)) = Some (Gval (Fuint 1) (global_word_1351 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1352 v : global_word_1352 v = global_word_0 v.
Proof. have E := global_closed_1352_value v.
 change (Some (Gval Fclock (global_word_0 v)) = Some (Gval Fclock (global_word_1352 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1353 v : global_word_1353 v = global_word_1 v.
Proof. have E := global_closed_1353_value v.
 change (Some (Gval (Fuint 1) (global_word_1 v)) = Some (Gval (Fuint 1) (global_word_1353 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1354 v : global_word_1354 v = global_word_0 v.
Proof. have E := global_closed_1354_value v.
 change (Some (Gval Fclock (global_word_0 v)) = Some (Gval Fclock (global_word_1354 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1355 v : global_word_1355 v = global_word_1 v.
Proof. have E := global_closed_1355_value v.
 change (Some (Gval (Fuint 1) (global_word_1 v)) = Some (Gval (Fuint 1) (global_word_1355 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1356 v : global_word_1356 v = global_word_0 v.
Proof. have E := global_closed_1356_value v.
 change (Some (Gval Fclock (global_word_0 v)) = Some (Gval Fclock (global_word_1356 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1357 v : global_word_1357 v = global_word_1 v.
Proof. have E := global_closed_1357_value v.
 change (Some (Gval (Fuint 1) (global_word_1 v)) = Some (Gval (Fuint 1) (global_word_1357 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1358 v : global_word_1358 v = global_word_0 v.
Proof. have E := global_closed_1358_value v.
 change (Some (Gval Fclock (global_word_0 v)) = Some (Gval Fclock (global_word_1358 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1359 v : global_word_1359 v = global_word_1 v.
Proof. have E := global_closed_1359_value v.
 change (Some (Gval (Fuint 1) (global_word_1 v)) = Some (Gval (Fuint 1) (global_word_1359 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1360 v : global_word_1360 v = global_word_0 v.
Proof. have E := global_closed_1360_value v.
 change (Some (Gval Fclock (global_word_0 v)) = Some (Gval Fclock (global_word_1360 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1361 v : global_word_1361 v = global_word_1 v.
Proof. have E := global_closed_1361_value v.
 change (Some (Gval (Fuint 1) (global_word_1 v)) = Some (Gval (Fuint 1) (global_word_1361 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1362 v : global_word_1362 v = global_word_0 v.
Proof. have E := global_closed_1362_value v.
 change (Some (Gval Fclock (global_word_0 v)) = Some (Gval Fclock (global_word_1362 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1363 v : global_word_1363 v = global_word_1 v.
Proof. have E := global_closed_1363_value v.
 change (Some (Gval (Fuint 1) (global_word_1 v)) = Some (Gval (Fuint 1) (global_word_1363 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1364 v : global_word_1364 v = global_word_0 v.
Proof. have E := global_closed_1364_value v.
 change (Some (Gval Fclock (global_word_0 v)) = Some (Gval Fclock (global_word_1364 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1365 v : global_word_1365 v = global_word_1 v.
Proof. have E := global_closed_1365_value v.
 change (Some (Gval (Fuint 1) (global_word_1 v)) = Some (Gval (Fuint 1) (global_word_1365 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1366 v : global_word_1366 v = global_word_0 v.
Proof. have E := global_closed_1366_value v.
 change (Some (Gval Fclock (global_word_0 v)) = Some (Gval Fclock (global_word_1366 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1367 v : global_word_1367 v = global_word_1 v.
Proof. have E := global_closed_1367_value v.
 change (Some (Gval (Fuint 1) (global_word_1 v)) = Some (Gval (Fuint 1) (global_word_1367 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1368 v : global_word_1368 v = global_word_0 v.
Proof. have E := global_closed_1368_value v.
 change (Some (Gval Fclock (global_word_0 v)) = Some (Gval Fclock (global_word_1368 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1369 v : global_word_1369 v = global_word_1 v.
Proof. have E := global_closed_1369_value v.
 change (Some (Gval (Fuint 1) (global_word_1 v)) = Some (Gval (Fuint 1) (global_word_1369 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1380 v : global_word_1380 v = global_word_1311 v. Proof. apply global_sync_1380. Qed.
Lemma wire_alias_1384 v : global_word_1384 v = global_word_1310 v. Proof. apply global_sync_1384. Qed.
Lemma wire_alias_1395 v : global_word_1395 v = global_word_1313 v. Proof. apply global_sync_1395. Qed.
Lemma wire_alias_1399 v : global_word_1399 v = global_word_1312 v. Proof. apply global_sync_1399. Qed.
Lemma wire_alias_1413 v : global_word_1413 v = global_word_1315 v. Proof. apply global_sync_1413. Qed.
Lemma wire_alias_1417 v : global_word_1417 v = global_word_1314 v. Proof. apply global_sync_1417. Qed.
Lemma wire_alias_1431 v : global_word_1431 v = global_word_1317 v. Proof. apply global_sync_1431. Qed.
Lemma wire_alias_1435 v : global_word_1435 v = global_word_1316 v. Proof. apply global_sync_1435. Qed.
Lemma wire_alias_1459 v : global_word_1459 v = global_word_1319 v. Proof. apply global_sync_1459. Qed.
Lemma wire_alias_1463 v : global_word_1463 v = global_word_1318 v. Proof. apply global_sync_1463. Qed.
Lemma wire_alias_1464 v : global_word_1464 v = global_word_1463 v.
Proof. have E := global_closed_1464_value v.
 change (Some (Gval Fclock (global_word_1463 v)) = Some (Gval Fclock (global_word_1464 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1465 v : global_word_1465 v = global_word_1459 v.
Proof. have E := global_closed_1465_value v.
 change (Some (Gval (Fuint 1) (global_word_1459 v)) = Some (Gval (Fuint 1) (global_word_1465 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1466 v : global_word_1466 v = global_word_1463 v.
Proof. have E := global_closed_1466_value v.
 change (Some (Gval Fclock (global_word_1463 v)) = Some (Gval Fclock (global_word_1466 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1467 v : global_word_1467 v = global_word_1459 v.
Proof. have E := global_closed_1467_value v.
 change (Some (Gval (Fuint 1) (global_word_1459 v)) = Some (Gval (Fuint 1) (global_word_1467 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1481 v : global_word_1481 v = global_word_1465 v. Proof. apply global_sync_1481. Qed.
Lemma wire_alias_1485 v : global_word_1485 v = global_word_1464 v. Proof. apply global_sync_1485. Qed.
Lemma wire_alias_1499 v : global_word_1499 v = global_word_1467 v. Proof. apply global_sync_1499. Qed.
Lemma wire_alias_1503 v : global_word_1503 v = global_word_1466 v. Proof. apply global_sync_1503. Qed.
Lemma wire_alias_1527 v : global_word_1527 v = global_word_1321 v. Proof. apply global_sync_1527. Qed.
Lemma wire_alias_1531 v : global_word_1531 v = global_word_1320 v. Proof. apply global_sync_1531. Qed.
Lemma wire_alias_1532 v : global_word_1532 v = global_word_1531 v.
Proof. have E := global_closed_1532_value v.
 change (Some (Gval Fclock (global_word_1531 v)) = Some (Gval Fclock (global_word_1532 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1533 v : global_word_1533 v = global_word_1527 v.
Proof. have E := global_closed_1533_value v.
 change (Some (Gval (Fuint 1) (global_word_1527 v)) = Some (Gval (Fuint 1) (global_word_1533 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1534 v : global_word_1534 v = global_word_1531 v.
Proof. have E := global_closed_1534_value v.
 change (Some (Gval Fclock (global_word_1531 v)) = Some (Gval Fclock (global_word_1534 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1535 v : global_word_1535 v = global_word_1527 v.
Proof. have E := global_closed_1535_value v.
 change (Some (Gval (Fuint 1) (global_word_1527 v)) = Some (Gval (Fuint 1) (global_word_1535 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1549 v : global_word_1549 v = global_word_1533 v. Proof. apply global_sync_1549. Qed.
Lemma wire_alias_1553 v : global_word_1553 v = global_word_1532 v. Proof. apply global_sync_1553. Qed.
Lemma wire_alias_1567 v : global_word_1567 v = global_word_1535 v. Proof. apply global_sync_1567. Qed.
Lemma wire_alias_1571 v : global_word_1571 v = global_word_1534 v. Proof. apply global_sync_1571. Qed.
Lemma wire_alias_1595 v : global_word_1595 v = global_word_1323 v. Proof. apply global_sync_1595. Qed.
Lemma wire_alias_1599 v : global_word_1599 v = global_word_1322 v. Proof. apply global_sync_1599. Qed.
Lemma wire_alias_1600 v : global_word_1600 v = global_word_1599 v.
Proof. have E := global_closed_1600_value v.
 change (Some (Gval Fclock (global_word_1599 v)) = Some (Gval Fclock (global_word_1600 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1601 v : global_word_1601 v = global_word_1595 v.
Proof. have E := global_closed_1601_value v.
 change (Some (Gval (Fuint 1) (global_word_1595 v)) = Some (Gval (Fuint 1) (global_word_1601 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1602 v : global_word_1602 v = global_word_1599 v.
Proof. have E := global_closed_1602_value v.
 change (Some (Gval Fclock (global_word_1599 v)) = Some (Gval Fclock (global_word_1602 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1603 v : global_word_1603 v = global_word_1595 v.
Proof. have E := global_closed_1603_value v.
 change (Some (Gval (Fuint 1) (global_word_1595 v)) = Some (Gval (Fuint 1) (global_word_1603 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1617 v : global_word_1617 v = global_word_1601 v. Proof. apply global_sync_1617. Qed.
Lemma wire_alias_1621 v : global_word_1621 v = global_word_1600 v. Proof. apply global_sync_1621. Qed.
Lemma wire_alias_1635 v : global_word_1635 v = global_word_1603 v. Proof. apply global_sync_1635. Qed.
Lemma wire_alias_1639 v : global_word_1639 v = global_word_1602 v. Proof. apply global_sync_1639. Qed.
Lemma wire_alias_1663 v : global_word_1663 v = global_word_1325 v. Proof. apply global_sync_1663. Qed.
Lemma wire_alias_1667 v : global_word_1667 v = global_word_1324 v. Proof. apply global_sync_1667. Qed.
Lemma wire_alias_1668 v : global_word_1668 v = global_word_1667 v.
Proof. have E := global_closed_1668_value v.
 change (Some (Gval Fclock (global_word_1667 v)) = Some (Gval Fclock (global_word_1668 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1669 v : global_word_1669 v = global_word_1663 v.
Proof. have E := global_closed_1669_value v.
 change (Some (Gval (Fuint 1) (global_word_1663 v)) = Some (Gval (Fuint 1) (global_word_1669 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1670 v : global_word_1670 v = global_word_1667 v.
Proof. have E := global_closed_1670_value v.
 change (Some (Gval Fclock (global_word_1667 v)) = Some (Gval Fclock (global_word_1670 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1671 v : global_word_1671 v = global_word_1663 v.
Proof. have E := global_closed_1671_value v.
 change (Some (Gval (Fuint 1) (global_word_1663 v)) = Some (Gval (Fuint 1) (global_word_1671 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1685 v : global_word_1685 v = global_word_1669 v. Proof. apply global_sync_1685. Qed.
Lemma wire_alias_1689 v : global_word_1689 v = global_word_1668 v. Proof. apply global_sync_1689. Qed.
Lemma wire_alias_1703 v : global_word_1703 v = global_word_1671 v. Proof. apply global_sync_1703. Qed.
Lemma wire_alias_1707 v : global_word_1707 v = global_word_1670 v. Proof. apply global_sync_1707. Qed.
Lemma wire_alias_1731 v : global_word_1731 v = global_word_1327 v. Proof. apply global_sync_1731. Qed.
Lemma wire_alias_1735 v : global_word_1735 v = global_word_1326 v. Proof. apply global_sync_1735. Qed.
Lemma wire_alias_1736 v : global_word_1736 v = global_word_1735 v.
Proof. have E := global_closed_1736_value v.
 change (Some (Gval Fclock (global_word_1735 v)) = Some (Gval Fclock (global_word_1736 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1737 v : global_word_1737 v = global_word_1731 v.
Proof. have E := global_closed_1737_value v.
 change (Some (Gval (Fuint 1) (global_word_1731 v)) = Some (Gval (Fuint 1) (global_word_1737 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1738 v : global_word_1738 v = global_word_1735 v.
Proof. have E := global_closed_1738_value v.
 change (Some (Gval Fclock (global_word_1735 v)) = Some (Gval Fclock (global_word_1738 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1739 v : global_word_1739 v = global_word_1731 v.
Proof. have E := global_closed_1739_value v.
 change (Some (Gval (Fuint 1) (global_word_1731 v)) = Some (Gval (Fuint 1) (global_word_1739 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1753 v : global_word_1753 v = global_word_1737 v. Proof. apply global_sync_1753. Qed.
Lemma wire_alias_1757 v : global_word_1757 v = global_word_1736 v. Proof. apply global_sync_1757. Qed.
Lemma wire_alias_1771 v : global_word_1771 v = global_word_1739 v. Proof. apply global_sync_1771. Qed.
Lemma wire_alias_1775 v : global_word_1775 v = global_word_1738 v. Proof. apply global_sync_1775. Qed.
Lemma wire_alias_1799 v : global_word_1799 v = global_word_1329 v. Proof. apply global_sync_1799. Qed.
Lemma wire_alias_1803 v : global_word_1803 v = global_word_1328 v. Proof. apply global_sync_1803. Qed.
Lemma wire_alias_1804 v : global_word_1804 v = global_word_1803 v.
Proof. have E := global_closed_1804_value v.
 change (Some (Gval Fclock (global_word_1803 v)) = Some (Gval Fclock (global_word_1804 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1805 v : global_word_1805 v = global_word_1799 v.
Proof. have E := global_closed_1805_value v.
 change (Some (Gval (Fuint 1) (global_word_1799 v)) = Some (Gval (Fuint 1) (global_word_1805 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1806 v : global_word_1806 v = global_word_1803 v.
Proof. have E := global_closed_1806_value v.
 change (Some (Gval Fclock (global_word_1803 v)) = Some (Gval Fclock (global_word_1806 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1807 v : global_word_1807 v = global_word_1799 v.
Proof. have E := global_closed_1807_value v.
 change (Some (Gval (Fuint 1) (global_word_1799 v)) = Some (Gval (Fuint 1) (global_word_1807 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1821 v : global_word_1821 v = global_word_1805 v. Proof. apply global_sync_1821. Qed.
Lemma wire_alias_1825 v : global_word_1825 v = global_word_1804 v. Proof. apply global_sync_1825. Qed.
Lemma wire_alias_1839 v : global_word_1839 v = global_word_1807 v. Proof. apply global_sync_1839. Qed.
Lemma wire_alias_1843 v : global_word_1843 v = global_word_1806 v. Proof. apply global_sync_1843. Qed.
Lemma wire_alias_1867 v : global_word_1867 v = global_word_1331 v. Proof. apply global_sync_1867. Qed.
Lemma wire_alias_1871 v : global_word_1871 v = global_word_1330 v. Proof. apply global_sync_1871. Qed.
Lemma wire_alias_1872 v : global_word_1872 v = global_word_1871 v.
Proof. have E := global_closed_1872_value v.
 change (Some (Gval Fclock (global_word_1871 v)) = Some (Gval Fclock (global_word_1872 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1873 v : global_word_1873 v = global_word_1867 v.
Proof. have E := global_closed_1873_value v.
 change (Some (Gval (Fuint 1) (global_word_1867 v)) = Some (Gval (Fuint 1) (global_word_1873 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1874 v : global_word_1874 v = global_word_1871 v.
Proof. have E := global_closed_1874_value v.
 change (Some (Gval Fclock (global_word_1871 v)) = Some (Gval Fclock (global_word_1874 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1875 v : global_word_1875 v = global_word_1867 v.
Proof. have E := global_closed_1875_value v.
 change (Some (Gval (Fuint 1) (global_word_1867 v)) = Some (Gval (Fuint 1) (global_word_1875 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1889 v : global_word_1889 v = global_word_1873 v. Proof. apply global_sync_1889. Qed.
Lemma wire_alias_1893 v : global_word_1893 v = global_word_1872 v. Proof. apply global_sync_1893. Qed.
Lemma wire_alias_1907 v : global_word_1907 v = global_word_1875 v. Proof. apply global_sync_1907. Qed.
Lemma wire_alias_1911 v : global_word_1911 v = global_word_1874 v. Proof. apply global_sync_1911. Qed.
Lemma wire_alias_1935 v : global_word_1935 v = global_word_1333 v. Proof. apply global_sync_1935. Qed.
Lemma wire_alias_1939 v : global_word_1939 v = global_word_1332 v. Proof. apply global_sync_1939. Qed.
Lemma wire_alias_1940 v : global_word_1940 v = global_word_1939 v.
Proof. have E := global_closed_1940_value v.
 change (Some (Gval Fclock (global_word_1939 v)) = Some (Gval Fclock (global_word_1940 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1941 v : global_word_1941 v = global_word_1935 v.
Proof. have E := global_closed_1941_value v.
 change (Some (Gval (Fuint 1) (global_word_1935 v)) = Some (Gval (Fuint 1) (global_word_1941 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1942 v : global_word_1942 v = global_word_1939 v.
Proof. have E := global_closed_1942_value v.
 change (Some (Gval Fclock (global_word_1939 v)) = Some (Gval Fclock (global_word_1942 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1943 v : global_word_1943 v = global_word_1935 v.
Proof. have E := global_closed_1943_value v.
 change (Some (Gval (Fuint 1) (global_word_1935 v)) = Some (Gval (Fuint 1) (global_word_1943 v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
Lemma wire_alias_1957 v : global_word_1957 v = global_word_1941 v. Proof. apply global_sync_1957. Qed.
Lemma wire_alias_1961 v : global_word_1961 v = global_word_1940 v. Proof. apply global_sync_1961. Qed.
Lemma wire_alias_1975 v : global_word_1975 v = global_word_1943 v. Proof. apply global_sync_1975. Qed.
Lemma wire_alias_1979 v : global_word_1979 v = global_word_1942 v. Proof. apply global_sync_1979. Qed.
Lemma wire_alias_1993 v : global_word_1993 v = global_word_1335 v. Proof. apply global_sync_1993. Qed.
Lemma wire_alias_1997 v : global_word_1997 v = global_word_1334 v. Proof. apply global_sync_1997. Qed.
Lemma wire_alias_2008 v : global_word_2008 v = global_word_1337 v. Proof. apply global_sync_2008. Qed.
Lemma wire_alias_2012 v : global_word_2012 v = global_word_1336 v. Proof. apply global_sync_2012. Qed.
Lemma wire_alias_2023 v : global_word_2023 v = global_word_1339 v. Proof. apply global_sync_2023. Qed.
Lemma wire_alias_2027 v : global_word_2027 v = global_word_1338 v. Proof. apply global_sync_2027. Qed.
Lemma wire_alias_2038 v : global_word_2038 v = global_word_1341 v. Proof. apply global_sync_2038. Qed.
Lemma wire_alias_2042 v : global_word_2042 v = global_word_1340 v. Proof. apply global_sync_2042. Qed.
Lemma wire_alias_2053 v : global_word_2053 v = global_word_1343 v. Proof. apply global_sync_2053. Qed.
Lemma wire_alias_2057 v : global_word_2057 v = global_word_1342 v. Proof. apply global_sync_2057. Qed.
Lemma wire_alias_2068 v : global_word_2068 v = global_word_1345 v. Proof. apply global_sync_2068. Qed.
Lemma wire_alias_2072 v : global_word_2072 v = global_word_1344 v. Proof. apply global_sync_2072. Qed.
Lemma wire_alias_2083 v : global_word_2083 v = global_word_1347 v. Proof. apply global_sync_2083. Qed.
Lemma wire_alias_2087 v : global_word_2087 v = global_word_1346 v. Proof. apply global_sync_2087. Qed.
Lemma wire_alias_2098 v : global_word_2098 v = global_word_1349 v. Proof. apply global_sync_2098. Qed.
Lemma wire_alias_2102 v : global_word_2102 v = global_word_1348 v. Proof. apply global_sync_2102. Qed.
Lemma wire_alias_2116 v : global_word_2116 v = global_word_1351 v. Proof. apply global_sync_2116. Qed.
Lemma wire_alias_2120 v : global_word_2120 v = global_word_1350 v. Proof. apply global_sync_2120. Qed.
Lemma wire_alias_2134 v : global_word_2134 v = global_word_1353 v. Proof. apply global_sync_2134. Qed.
Lemma wire_alias_2138 v : global_word_2138 v = global_word_1352 v. Proof. apply global_sync_2138. Qed.
Lemma wire_alias_2149 v : global_word_2149 v = global_word_1355 v. Proof. apply global_sync_2149. Qed.
Lemma wire_alias_2153 v : global_word_2153 v = global_word_1354 v. Proof. apply global_sync_2153. Qed.
Lemma wire_alias_2164 v : global_word_2164 v = global_word_1357 v. Proof. apply global_sync_2164. Qed.
Lemma wire_alias_2168 v : global_word_2168 v = global_word_1356 v. Proof. apply global_sync_2168. Qed.
Lemma wire_alias_2179 v : global_word_2179 v = global_word_1359 v. Proof. apply global_sync_2179. Qed.
Lemma wire_alias_2183 v : global_word_2183 v = global_word_1358 v. Proof. apply global_sync_2183. Qed.
Lemma wire_alias_2194 v : global_word_2194 v = global_word_1361 v. Proof. apply global_sync_2194. Qed.
Lemma wire_alias_2198 v : global_word_2198 v = global_word_1360 v. Proof. apply global_sync_2198. Qed.
Lemma wire_alias_2212 v : global_word_2212 v = global_word_1363 v. Proof. apply global_sync_2212. Qed.
Lemma wire_alias_2216 v : global_word_2216 v = global_word_1362 v. Proof. apply global_sync_2216. Qed.
Lemma wire_alias_2227 v : global_word_2227 v = global_word_1365 v. Proof. apply global_sync_2227. Qed.
Lemma wire_alias_2231 v : global_word_2231 v = global_word_1364 v. Proof. apply global_sync_2231. Qed.
Lemma wire_alias_2242 v : global_word_2242 v = global_word_1367 v. Proof. apply global_sync_2242. Qed.
Lemma wire_alias_2246 v : global_word_2246 v = global_word_1366 v. Proof. apply global_sync_2246. Qed.
Lemma wire_alias_2257 v : global_word_2257 v = global_word_1369 v. Proof. apply global_sync_2257. Qed.
Lemma wire_alias_2261 v : global_word_2261 v = global_word_1368 v. Proof. apply global_sync_2261. Qed.
