From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalProgressTypes GlobalFieldSteps GlobalScalarSteps GlobalProgress.
Local Open Scope N_scope.
From SmallMultiplier Require Import GlobalTypeProgress.
Lemma global_rank_chunk_2 invalid snapshot final v level (prior:global_ranked v level snapshot) (sizes:global_leaf_sizes v)
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 List.Forall (fun index => (global_rank_at index <= S level)%coq_nat -> global_value_at index final = Some (global_target_at index v)) (List.seq 400 200).
Proof.
 constructor.
 - intro enough. exact (global_progress_400 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_401 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_402 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_403 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_404 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_405 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_406 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_407 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_408 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_409 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_410 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_411 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_412 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_413 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_414 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_415 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_416 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_417 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_418 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_419 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_420 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_421 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_422 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_423 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_424 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_425 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_426 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_427 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_428 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_429 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_430 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_431 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_432 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_433 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_434 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_435 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_436 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_437 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_438 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_439 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_440 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_441 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_442 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_443 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_444 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_445 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_446 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_447 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_448 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_449 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_450 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_451 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_452 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_453 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_454 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_455 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_456 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_457 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_458 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_459 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_460 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_461 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_462 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_463 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_464 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_465 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_466 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_467 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_468 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_469 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_470 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_471 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_472 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_473 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_474 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_475 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_476 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_477 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_478 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_479 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_480 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_481 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_482 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_483 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_484 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_485 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_486 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_487 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_488 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_489 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_490 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_491 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_492 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_493 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_494 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_495 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_496 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_497 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_498 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_499 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_500 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_501 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_502 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_503 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_504 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_505 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_506 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_507 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_508 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_509 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_510 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_511 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_512 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_513 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_514 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_515 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_516 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_517 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_518 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_519 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_520 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_521 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_522 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_523 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_524 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_525 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_526 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_527 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_528 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_529 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_530 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_531 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_532 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_533 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_534 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_535 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_536 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_537 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_538 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_539 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_540 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_541 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_542 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_543 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_544 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_545 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_546 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_547 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_548 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_549 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_550 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_551 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_552 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_553 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_554 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_555 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_556 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_557 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_558 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_559 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_560 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_561 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_562 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_563 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_564 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_565 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_566 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_567 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_568 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_569 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_570 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_571 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_572 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_573 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_574 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_575 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_576 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_577 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_578 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_579 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_580 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_581 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_582 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_583 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_584 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_585 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_586 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_587 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_588 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_589 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_590 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_591 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_592 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_593 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_594 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_595 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_596 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_597 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_598 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_599 invalid snapshot final v level prior types sizes enough ran).
 constructor.
Qed.
Lemma global_type_chunk_2 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 List.Forall (fun index => global_port_at index=true -> option_map type_of_val (global_value_at index final)=Some(Gtyp(global_type_at index))) (List.seq 400 200).
Proof.
 constructor.
 - intro included. exact (global_type_progress_400 invalid snapshot final types ran).
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
 - intro included. exact (global_type_progress_411 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_414 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_418 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_421 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_425 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_428 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_431 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_434 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_437 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_439 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_442 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_444 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_447 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_449 invalid snapshot final types ran).
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
 - intro included. exact (global_type_progress_460 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_463 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_466 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_469 invalid snapshot final types ran).
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
 - intro included. exact (global_type_progress_480 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_483 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_487 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_490 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_494 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_497 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_500 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_503 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_506 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_508 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_511 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_513 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_516 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_518 invalid snapshot final types ran).
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
 - intro included. exact (global_type_progress_529 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_532 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_535 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_538 invalid snapshot final types ran).
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
 - intro included. exact (global_type_progress_549 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_552 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_556 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_559 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_563 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_566 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_569 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_572 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_575 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_577 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_580 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_582 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_585 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_587 invalid snapshot final types ran).
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
 - intro included. exact (global_type_progress_598 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
Qed.
