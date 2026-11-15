From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalProgressTypes GlobalFieldSteps GlobalScalarSteps GlobalProgress.
Local Open Scope N_scope.
Lemma global_type_progress_278 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 278%nat final) = Some (Gtyp (global_type_at 278%nat)).
Proof.
 have Typed := types 278%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_278_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_281 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 281%nat final) = Some (Gtyp (global_type_at 281%nat)).
Proof.
 have Typed := types 281%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_281_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_289 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 289%nat final) = Some (Gtyp (global_type_at 289%nat)).
Proof.
 have Typed := types 289%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_289_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::7] 4 final) = Some (Gtyp (global_type_at 289%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_293 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 293%nat final) = Some (Gtyp (global_type_at 293%nat)).
Proof.
 have Typed := types 293%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_293_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::7] 5 final) = Some (Gtyp (global_type_at 293%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_296 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 296%nat final) = Some (Gtyp (global_type_at 296%nat)).
Proof.
 have Typed := types 296%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_296_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_299 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 299%nat final) = Some (Gtyp (global_type_at 299%nat)).
Proof.
 have Typed := types 299%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_299_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_307 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 307%nat final) = Some (Gtyp (global_type_at 307%nat)).
Proof.
 have Typed := types 307%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_307_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::8] 4 final) = Some (Gtyp (global_type_at 307%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_311 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 311%nat final) = Some (Gtyp (global_type_at 311%nat)).
Proof.
 have Typed := types 311%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_311_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::8] 5 final) = Some (Gtyp (global_type_at 311%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_314 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 314%nat final) = Some (Gtyp (global_type_at 314%nat)).
Proof.
 have Typed := types 314%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_314_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_317 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 317%nat final) = Some (Gtyp (global_type_at 317%nat)).
Proof.
 have Typed := types 317%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_317_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_320 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 320%nat final) = Some (Gtyp (global_type_at 320%nat)).
Proof.
 have Typed := types 320%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_320_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_331 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 331%nat final) = Some (Gtyp (global_type_at 331%nat)).
Proof.
 have Typed := types 331%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_331_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::9] 5 final) = Some (Gtyp (global_type_at 331%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_335 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 335%nat final) = Some (Gtyp (global_type_at 335%nat)).
Proof.
 have Typed := types 335%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_335_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::9] 6 final) = Some (Gtyp (global_type_at 335%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_338 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 338%nat final) = Some (Gtyp (global_type_at 338%nat)).
Proof.
 have Typed := types 338%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_338_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_341 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 341%nat final) = Some (Gtyp (global_type_at 341%nat)).
Proof.
 have Typed := types 341%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_341_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_344 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 344%nat final) = Some (Gtyp (global_type_at 344%nat)).
Proof.
 have Typed := types 344%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_344_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_355 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 355%nat final) = Some (Gtyp (global_type_at 355%nat)).
Proof.
 have Typed := types 355%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_355_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::10] 5 final) = Some (Gtyp (global_type_at 355%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_359 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 359%nat final) = Some (Gtyp (global_type_at 359%nat)).
Proof.
 have Typed := types 359%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_359_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::10] 6 final) = Some (Gtyp (global_type_at 359%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_362 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 362%nat final) = Some (Gtyp (global_type_at 362%nat)).
Proof.
 have Typed := types 362%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_362_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_365 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 365%nat final) = Some (Gtyp (global_type_at 365%nat)).
Proof.
 have Typed := types 365%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_365_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_368 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 368%nat final) = Some (Gtyp (global_type_at 368%nat)).
Proof.
 have Typed := types 368%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_368_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_370 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 370%nat final) = Some (Gtyp (global_type_at 370%nat)).
Proof.
 have Typed := types 370%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_370_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_373 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 373%nat final) = Some (Gtyp (global_type_at 373%nat)).
Proof.
 have Typed := types 373%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_373_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_375 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 375%nat final) = Some (Gtyp (global_type_at 375%nat)).
Proof.
 have Typed := types 375%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_375_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_378 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 378%nat final) = Some (Gtyp (global_type_at 378%nat)).
Proof.
 have Typed := types 378%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_378_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_380 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 380%nat final) = Some (Gtyp (global_type_at 380%nat)).
Proof.
 have Typed := types 380%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_380_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_391 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 391%nat final) = Some (Gtyp (global_type_at 391%nat)).
Proof.
 have Typed := types 391%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_391_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::10;11] 5 final) = Some (Gtyp (global_type_at 391%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_394 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 394%nat final) = Some (Gtyp (global_type_at 394%nat)).
Proof.
 have Typed := types 394%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_394_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_397 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 397%nat final) = Some (Gtyp (global_type_at 397%nat)).
Proof.
 have Typed := types 397%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_397_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_400 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 400%nat final) = Some (Gtyp (global_type_at 400%nat)).
Proof.
 have Typed := types 400%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_400_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_411 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 411%nat final) = Some (Gtyp (global_type_at 411%nat)).
Proof.
 have Typed := types 411%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_411_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::11;11] 5 final) = Some (Gtyp (global_type_at 411%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_414 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 414%nat final) = Some (Gtyp (global_type_at 414%nat)).
Proof.
 have Typed := types 414%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_414_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::11] 7 final) = Some (Gtyp (global_type_at 414%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_418 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 418%nat final) = Some (Gtyp (global_type_at 418%nat)).
Proof.
 have Typed := types 418%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_418_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::10;11] 6 final) = Some (Gtyp (global_type_at 418%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_421 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 421%nat final) = Some (Gtyp (global_type_at 421%nat)).
Proof.
 have Typed := types 421%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_421_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::11] 8 final) = Some (Gtyp (global_type_at 421%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_425 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 425%nat final) = Some (Gtyp (global_type_at 425%nat)).
Proof.
 have Typed := types 425%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_425_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::11;11] 6 final) = Some (Gtyp (global_type_at 425%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_428 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 428%nat final) = Some (Gtyp (global_type_at 428%nat)).
Proof.
 have Typed := types 428%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_428_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::11] 9 final) = Some (Gtyp (global_type_at 428%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_431 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 431%nat final) = Some (Gtyp (global_type_at 431%nat)).
Proof.
 have Typed := types 431%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_431_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_434 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 434%nat final) = Some (Gtyp (global_type_at 434%nat)).
Proof.
 have Typed := types 434%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_434_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_437 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 437%nat final) = Some (Gtyp (global_type_at 437%nat)).
Proof.
 have Typed := types 437%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_437_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_439 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 439%nat final) = Some (Gtyp (global_type_at 439%nat)).
Proof.
 have Typed := types 439%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_439_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_442 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 442%nat final) = Some (Gtyp (global_type_at 442%nat)).
Proof.
 have Typed := types 442%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_442_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_444 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 444%nat final) = Some (Gtyp (global_type_at 444%nat)).
Proof.
 have Typed := types 444%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_444_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_447 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 447%nat final) = Some (Gtyp (global_type_at 447%nat)).
Proof.
 have Typed := types 447%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_447_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_449 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 449%nat final) = Some (Gtyp (global_type_at 449%nat)).
Proof.
 have Typed := types 449%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_449_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_460 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 460%nat final) = Some (Gtyp (global_type_at 460%nat)).
Proof.
 have Typed := types 460%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_460_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::10;12] 5 final) = Some (Gtyp (global_type_at 460%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_463 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 463%nat final) = Some (Gtyp (global_type_at 463%nat)).
Proof.
 have Typed := types 463%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_463_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_466 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 466%nat final) = Some (Gtyp (global_type_at 466%nat)).
Proof.
 have Typed := types 466%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_466_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_469 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 469%nat final) = Some (Gtyp (global_type_at 469%nat)).
Proof.
 have Typed := types 469%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_469_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_480 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 480%nat final) = Some (Gtyp (global_type_at 480%nat)).
Proof.
 have Typed := types 480%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_480_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::11;12] 5 final) = Some (Gtyp (global_type_at 480%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_483 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 483%nat final) = Some (Gtyp (global_type_at 483%nat)).
Proof.
 have Typed := types 483%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_483_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::12] 7 final) = Some (Gtyp (global_type_at 483%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_487 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 487%nat final) = Some (Gtyp (global_type_at 487%nat)).
Proof.
 have Typed := types 487%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_487_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::10;12] 6 final) = Some (Gtyp (global_type_at 487%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_490 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 490%nat final) = Some (Gtyp (global_type_at 490%nat)).
Proof.
 have Typed := types 490%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_490_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::12] 8 final) = Some (Gtyp (global_type_at 490%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_494 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 494%nat final) = Some (Gtyp (global_type_at 494%nat)).
Proof.
 have Typed := types 494%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_494_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::11;12] 6 final) = Some (Gtyp (global_type_at 494%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_497 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 497%nat final) = Some (Gtyp (global_type_at 497%nat)).
Proof.
 have Typed := types 497%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_497_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::12] 9 final) = Some (Gtyp (global_type_at 497%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_500 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 500%nat final) = Some (Gtyp (global_type_at 500%nat)).
Proof.
 have Typed := types 500%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_500_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_503 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 503%nat final) = Some (Gtyp (global_type_at 503%nat)).
Proof.
 have Typed := types 503%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_503_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_506 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 506%nat final) = Some (Gtyp (global_type_at 506%nat)).
Proof.
 have Typed := types 506%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_506_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_508 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 508%nat final) = Some (Gtyp (global_type_at 508%nat)).
Proof.
 have Typed := types 508%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_508_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_511 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 511%nat final) = Some (Gtyp (global_type_at 511%nat)).
Proof.
 have Typed := types 511%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_511_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_513 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 513%nat final) = Some (Gtyp (global_type_at 513%nat)).
Proof.
 have Typed := types 513%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_513_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_516 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 516%nat final) = Some (Gtyp (global_type_at 516%nat)).
Proof.
 have Typed := types 516%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_516_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_518 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 518%nat final) = Some (Gtyp (global_type_at 518%nat)).
Proof.
 have Typed := types 518%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_518_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_529 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 529%nat final) = Some (Gtyp (global_type_at 529%nat)).
Proof.
 have Typed := types 529%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_529_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::10;13] 5 final) = Some (Gtyp (global_type_at 529%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_532 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 532%nat final) = Some (Gtyp (global_type_at 532%nat)).
Proof.
 have Typed := types 532%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_532_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_535 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 535%nat final) = Some (Gtyp (global_type_at 535%nat)).
Proof.
 have Typed := types 535%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_535_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_538 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 538%nat final) = Some (Gtyp (global_type_at 538%nat)).
Proof.
 have Typed := types 538%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_538_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_549 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 549%nat final) = Some (Gtyp (global_type_at 549%nat)).
Proof.
 have Typed := types 549%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_549_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::11;13] 5 final) = Some (Gtyp (global_type_at 549%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_552 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 552%nat final) = Some (Gtyp (global_type_at 552%nat)).
Proof.
 have Typed := types 552%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_552_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::13] 7 final) = Some (Gtyp (global_type_at 552%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_556 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 556%nat final) = Some (Gtyp (global_type_at 556%nat)).
Proof.
 have Typed := types 556%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_556_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::10;13] 6 final) = Some (Gtyp (global_type_at 556%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_559 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 559%nat final) = Some (Gtyp (global_type_at 559%nat)).
Proof.
 have Typed := types 559%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_559_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::13] 8 final) = Some (Gtyp (global_type_at 559%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_563 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 563%nat final) = Some (Gtyp (global_type_at 563%nat)).
Proof.
 have Typed := types 563%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_563_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::11;13] 6 final) = Some (Gtyp (global_type_at 563%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_566 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 566%nat final) = Some (Gtyp (global_type_at 566%nat)).
Proof.
 have Typed := types 566%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_566_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::13] 9 final) = Some (Gtyp (global_type_at 566%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_569 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 569%nat final) = Some (Gtyp (global_type_at 569%nat)).
Proof.
 have Typed := types 569%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_569_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_572 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 572%nat final) = Some (Gtyp (global_type_at 572%nat)).
Proof.
 have Typed := types 572%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_572_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_575 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 575%nat final) = Some (Gtyp (global_type_at 575%nat)).
Proof.
 have Typed := types 575%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_575_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_577 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 577%nat final) = Some (Gtyp (global_type_at 577%nat)).
Proof.
 have Typed := types 577%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_577_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_580 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 580%nat final) = Some (Gtyp (global_type_at 580%nat)).
Proof.
 have Typed := types 580%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_580_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_582 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 582%nat final) = Some (Gtyp (global_type_at 582%nat)).
Proof.
 have Typed := types 582%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_582_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_585 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 585%nat final) = Some (Gtyp (global_type_at 585%nat)).
Proof.
 have Typed := types 585%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_585_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_587 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 587%nat final) = Some (Gtyp (global_type_at 587%nat)).
Proof.
 have Typed := types 587%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_587_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_598 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 598%nat final) = Some (Gtyp (global_type_at 598%nat)).
Proof.
 have Typed := types 598%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_598_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::10;14] 5 final) = Some (Gtyp (global_type_at 598%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_601 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 601%nat final) = Some (Gtyp (global_type_at 601%nat)).
Proof.
 have Typed := types 601%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_601_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_604 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 604%nat final) = Some (Gtyp (global_type_at 604%nat)).
Proof.
 have Typed := types 604%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_604_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_607 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 607%nat final) = Some (Gtyp (global_type_at 607%nat)).
Proof.
 have Typed := types 607%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_607_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_618 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 618%nat final) = Some (Gtyp (global_type_at 618%nat)).
Proof.
 have Typed := types 618%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_618_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::11;14] 5 final) = Some (Gtyp (global_type_at 618%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_621 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 621%nat final) = Some (Gtyp (global_type_at 621%nat)).
Proof.
 have Typed := types 621%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_621_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::14] 7 final) = Some (Gtyp (global_type_at 621%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_625 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 625%nat final) = Some (Gtyp (global_type_at 625%nat)).
Proof.
 have Typed := types 625%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_625_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::10;14] 6 final) = Some (Gtyp (global_type_at 625%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_628 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 628%nat final) = Some (Gtyp (global_type_at 628%nat)).
Proof.
 have Typed := types 628%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_628_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::14] 8 final) = Some (Gtyp (global_type_at 628%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_632 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 632%nat final) = Some (Gtyp (global_type_at 632%nat)).
Proof.
 have Typed := types 632%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_632_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::11;14] 6 final) = Some (Gtyp (global_type_at 632%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_635 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 635%nat final) = Some (Gtyp (global_type_at 635%nat)).
Proof.
 have Typed := types 635%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_635_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::14] 9 final) = Some (Gtyp (global_type_at 635%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_638 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 638%nat final) = Some (Gtyp (global_type_at 638%nat)).
Proof.
 have Typed := types 638%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_638_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_641 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 641%nat final) = Some (Gtyp (global_type_at 641%nat)).
Proof.
 have Typed := types 641%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_641_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_644 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 644%nat final) = Some (Gtyp (global_type_at 644%nat)).
Proof.
 have Typed := types 644%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_644_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_646 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 646%nat final) = Some (Gtyp (global_type_at 646%nat)).
Proof.
 have Typed := types 646%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_646_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_649 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 649%nat final) = Some (Gtyp (global_type_at 649%nat)).
Proof.
 have Typed := types 649%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_649_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_651 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 651%nat final) = Some (Gtyp (global_type_at 651%nat)).
Proof.
 have Typed := types 651%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_651_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_654 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 654%nat final) = Some (Gtyp (global_type_at 654%nat)).
Proof.
 have Typed := types 654%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_654_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_656 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 656%nat final) = Some (Gtyp (global_type_at 656%nat)).
Proof.
 have Typed := types 656%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_656_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_667 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 667%nat final) = Some (Gtyp (global_type_at 667%nat)).
Proof.
 have Typed := types 667%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_667_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::10;15] 5 final) = Some (Gtyp (global_type_at 667%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_670 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 670%nat final) = Some (Gtyp (global_type_at 670%nat)).
Proof.
 have Typed := types 670%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_670_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_673 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 673%nat final) = Some (Gtyp (global_type_at 673%nat)).
Proof.
 have Typed := types 673%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_673_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_676 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 676%nat final) = Some (Gtyp (global_type_at 676%nat)).
Proof.
 have Typed := types 676%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_676_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_687 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 687%nat final) = Some (Gtyp (global_type_at 687%nat)).
Proof.
 have Typed := types 687%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_687_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::11;15] 5 final) = Some (Gtyp (global_type_at 687%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_690 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 690%nat final) = Some (Gtyp (global_type_at 690%nat)).
Proof.
 have Typed := types 690%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_690_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::15] 7 final) = Some (Gtyp (global_type_at 690%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_694 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 694%nat final) = Some (Gtyp (global_type_at 694%nat)).
Proof.
 have Typed := types 694%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_694_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::10;15] 6 final) = Some (Gtyp (global_type_at 694%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_697 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 697%nat final) = Some (Gtyp (global_type_at 697%nat)).
Proof.
 have Typed := types 697%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_697_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::15] 8 final) = Some (Gtyp (global_type_at 697%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_701 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 701%nat final) = Some (Gtyp (global_type_at 701%nat)).
Proof.
 have Typed := types 701%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_701_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::11;15] 6 final) = Some (Gtyp (global_type_at 701%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_704 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 704%nat final) = Some (Gtyp (global_type_at 704%nat)).
Proof.
 have Typed := types 704%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_704_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::15] 9 final) = Some (Gtyp (global_type_at 704%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_707 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 707%nat final) = Some (Gtyp (global_type_at 707%nat)).
Proof.
 have Typed := types 707%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_707_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_710 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 710%nat final) = Some (Gtyp (global_type_at 710%nat)).
Proof.
 have Typed := types 710%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_710_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_713 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 713%nat final) = Some (Gtyp (global_type_at 713%nat)).
Proof.
 have Typed := types 713%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_713_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_715 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 715%nat final) = Some (Gtyp (global_type_at 715%nat)).
Proof.
 have Typed := types 715%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_715_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_718 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 718%nat final) = Some (Gtyp (global_type_at 718%nat)).
Proof.
 have Typed := types 718%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_718_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_720 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 720%nat final) = Some (Gtyp (global_type_at 720%nat)).
Proof.
 have Typed := types 720%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_720_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_723 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 723%nat final) = Some (Gtyp (global_type_at 723%nat)).
Proof.
 have Typed := types 723%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_723_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_725 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 725%nat final) = Some (Gtyp (global_type_at 725%nat)).
Proof.
 have Typed := types 725%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_725_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_736 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 736%nat final) = Some (Gtyp (global_type_at 736%nat)).
Proof.
 have Typed := types 736%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_736_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::10;16] 5 final) = Some (Gtyp (global_type_at 736%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_739 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 739%nat final) = Some (Gtyp (global_type_at 739%nat)).
Proof.
 have Typed := types 739%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_739_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_742 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 742%nat final) = Some (Gtyp (global_type_at 742%nat)).
Proof.
 have Typed := types 742%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_742_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_745 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 745%nat final) = Some (Gtyp (global_type_at 745%nat)).
Proof.
 have Typed := types 745%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_745_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_756 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 756%nat final) = Some (Gtyp (global_type_at 756%nat)).
Proof.
 have Typed := types 756%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_756_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::11;16] 5 final) = Some (Gtyp (global_type_at 756%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_759 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 759%nat final) = Some (Gtyp (global_type_at 759%nat)).
Proof.
 have Typed := types 759%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_759_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::16] 7 final) = Some (Gtyp (global_type_at 759%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_763 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 763%nat final) = Some (Gtyp (global_type_at 763%nat)).
Proof.
 have Typed := types 763%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_763_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::10;16] 6 final) = Some (Gtyp (global_type_at 763%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_766 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 766%nat final) = Some (Gtyp (global_type_at 766%nat)).
Proof.
 have Typed := types 766%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_766_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::16] 8 final) = Some (Gtyp (global_type_at 766%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_770 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 770%nat final) = Some (Gtyp (global_type_at 770%nat)).
Proof.
 have Typed := types 770%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_770_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::11;16] 6 final) = Some (Gtyp (global_type_at 770%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_773 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 773%nat final) = Some (Gtyp (global_type_at 773%nat)).
Proof.
 have Typed := types 773%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_773_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::16] 9 final) = Some (Gtyp (global_type_at 773%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_776 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 776%nat final) = Some (Gtyp (global_type_at 776%nat)).
Proof.
 have Typed := types 776%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_776_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_779 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 779%nat final) = Some (Gtyp (global_type_at 779%nat)).
Proof.
 have Typed := types 779%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_779_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_782 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 782%nat final) = Some (Gtyp (global_type_at 782%nat)).
Proof.
 have Typed := types 782%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_782_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_784 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 784%nat final) = Some (Gtyp (global_type_at 784%nat)).
Proof.
 have Typed := types 784%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_784_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_787 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 787%nat final) = Some (Gtyp (global_type_at 787%nat)).
Proof.
 have Typed := types 787%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_787_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_789 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 789%nat final) = Some (Gtyp (global_type_at 789%nat)).
Proof.
 have Typed := types 789%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_789_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_792 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 792%nat final) = Some (Gtyp (global_type_at 792%nat)).
Proof.
 have Typed := types 792%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_792_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_794 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 794%nat final) = Some (Gtyp (global_type_at 794%nat)).
Proof.
 have Typed := types 794%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_794_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_805 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 805%nat final) = Some (Gtyp (global_type_at 805%nat)).
Proof.
 have Typed := types 805%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_805_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::10;17] 5 final) = Some (Gtyp (global_type_at 805%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_808 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 808%nat final) = Some (Gtyp (global_type_at 808%nat)).
Proof.
 have Typed := types 808%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_808_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_811 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 811%nat final) = Some (Gtyp (global_type_at 811%nat)).
Proof.
 have Typed := types 811%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_811_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_814 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 814%nat final) = Some (Gtyp (global_type_at 814%nat)).
Proof.
 have Typed := types 814%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_814_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_825 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 825%nat final) = Some (Gtyp (global_type_at 825%nat)).
Proof.
 have Typed := types 825%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_825_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::11;17] 5 final) = Some (Gtyp (global_type_at 825%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_828 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 828%nat final) = Some (Gtyp (global_type_at 828%nat)).
Proof.
 have Typed := types 828%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_828_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::17] 7 final) = Some (Gtyp (global_type_at 828%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_832 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 832%nat final) = Some (Gtyp (global_type_at 832%nat)).
Proof.
 have Typed := types 832%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_832_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::10;17] 6 final) = Some (Gtyp (global_type_at 832%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_835 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 835%nat final) = Some (Gtyp (global_type_at 835%nat)).
Proof.
 have Typed := types 835%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_835_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::17] 8 final) = Some (Gtyp (global_type_at 835%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_839 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 839%nat final) = Some (Gtyp (global_type_at 839%nat)).
Proof.
 have Typed := types 839%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_839_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::11;17] 6 final) = Some (Gtyp (global_type_at 839%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_842 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 842%nat final) = Some (Gtyp (global_type_at 842%nat)).
Proof.
 have Typed := types 842%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_842_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::17] 9 final) = Some (Gtyp (global_type_at 842%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_845 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 845%nat final) = Some (Gtyp (global_type_at 845%nat)).
Proof.
 have Typed := types 845%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_845_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_848 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 848%nat final) = Some (Gtyp (global_type_at 848%nat)).
Proof.
 have Typed := types 848%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_848_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_851 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 851%nat final) = Some (Gtyp (global_type_at 851%nat)).
Proof.
 have Typed := types 851%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_851_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_853 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 853%nat final) = Some (Gtyp (global_type_at 853%nat)).
Proof.
 have Typed := types 853%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_853_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_856 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 856%nat final) = Some (Gtyp (global_type_at 856%nat)).
Proof.
 have Typed := types 856%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_856_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_858 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 858%nat final) = Some (Gtyp (global_type_at 858%nat)).
Proof.
 have Typed := types 858%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_858_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_861 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 861%nat final) = Some (Gtyp (global_type_at 861%nat)).
Proof.
 have Typed := types 861%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_861_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_863 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 863%nat final) = Some (Gtyp (global_type_at 863%nat)).
Proof.
 have Typed := types 863%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_863_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_874 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 874%nat final) = Some (Gtyp (global_type_at 874%nat)).
Proof.
 have Typed := types 874%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_874_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::10;18] 5 final) = Some (Gtyp (global_type_at 874%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_877 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 877%nat final) = Some (Gtyp (global_type_at 877%nat)).
Proof.
 have Typed := types 877%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_877_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_880 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 880%nat final) = Some (Gtyp (global_type_at 880%nat)).
Proof.
 have Typed := types 880%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_880_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_883 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 883%nat final) = Some (Gtyp (global_type_at 883%nat)).
Proof.
 have Typed := types 883%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_883_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_894 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 894%nat final) = Some (Gtyp (global_type_at 894%nat)).
Proof.
 have Typed := types 894%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_894_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::11;18] 5 final) = Some (Gtyp (global_type_at 894%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_897 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 897%nat final) = Some (Gtyp (global_type_at 897%nat)).
Proof.
 have Typed := types 897%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_897_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::18] 7 final) = Some (Gtyp (global_type_at 897%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_901 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 901%nat final) = Some (Gtyp (global_type_at 901%nat)).
Proof.
 have Typed := types 901%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_901_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::10;18] 6 final) = Some (Gtyp (global_type_at 901%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_904 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 904%nat final) = Some (Gtyp (global_type_at 904%nat)).
Proof.
 have Typed := types 904%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_904_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::18] 8 final) = Some (Gtyp (global_type_at 904%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_908 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 908%nat final) = Some (Gtyp (global_type_at 908%nat)).
Proof.
 have Typed := types 908%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_908_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::11;18] 6 final) = Some (Gtyp (global_type_at 908%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_911 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 911%nat final) = Some (Gtyp (global_type_at 911%nat)).
Proof.
 have Typed := types 911%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_911_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::18] 9 final) = Some (Gtyp (global_type_at 911%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_914 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 914%nat final) = Some (Gtyp (global_type_at 914%nat)).
Proof.
 have Typed := types 914%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_914_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_917 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 917%nat final) = Some (Gtyp (global_type_at 917%nat)).
Proof.
 have Typed := types 917%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_917_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_920 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 920%nat final) = Some (Gtyp (global_type_at 920%nat)).
Proof.
 have Typed := types 920%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_920_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_931 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 931%nat final) = Some (Gtyp (global_type_at 931%nat)).
Proof.
 have Typed := types 931%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_931_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::19] 5 final) = Some (Gtyp (global_type_at 931%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_935 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 935%nat final) = Some (Gtyp (global_type_at 935%nat)).
Proof.
 have Typed := types 935%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_935_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::19] 6 final) = Some (Gtyp (global_type_at 935%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_938 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 938%nat final) = Some (Gtyp (global_type_at 938%nat)).
Proof.
 have Typed := types 938%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_938_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_941 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 941%nat final) = Some (Gtyp (global_type_at 941%nat)).
Proof.
 have Typed := types 941%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_941_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_949 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 949%nat final) = Some (Gtyp (global_type_at 949%nat)).
Proof.
 have Typed := types 949%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_949_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::20] 4 final) = Some (Gtyp (global_type_at 949%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_953 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 953%nat final) = Some (Gtyp (global_type_at 953%nat)).
Proof.
 have Typed := types 953%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_953_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::20] 5 final) = Some (Gtyp (global_type_at 953%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_956 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 956%nat final) = Some (Gtyp (global_type_at 956%nat)).
Proof.
 have Typed := types 956%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_956_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_959 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 959%nat final) = Some (Gtyp (global_type_at 959%nat)).
Proof.
 have Typed := types 959%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_959_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_967 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 967%nat final) = Some (Gtyp (global_type_at 967%nat)).
Proof.
 have Typed := types 967%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_967_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::21] 4 final) = Some (Gtyp (global_type_at 967%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_971 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 971%nat final) = Some (Gtyp (global_type_at 971%nat)).
Proof.
 have Typed := types 971%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_971_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::21] 5 final) = Some (Gtyp (global_type_at 971%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_974 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 974%nat final) = Some (Gtyp (global_type_at 974%nat)).
Proof.
 have Typed := types 974%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_974_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_977 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 977%nat final) = Some (Gtyp (global_type_at 977%nat)).
Proof.
 have Typed := types 977%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_977_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_985 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 985%nat final) = Some (Gtyp (global_type_at 985%nat)).
Proof.
 have Typed := types 985%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_985_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::22] 4 final) = Some (Gtyp (global_type_at 985%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_989 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 989%nat final) = Some (Gtyp (global_type_at 989%nat)).
Proof.
 have Typed := types 989%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_989_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::22] 5 final) = Some (Gtyp (global_type_at 989%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_992 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 992%nat final) = Some (Gtyp (global_type_at 992%nat)).
Proof.
 have Typed := types 992%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_992_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_995 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 995%nat final) = Some (Gtyp (global_type_at 995%nat)).
Proof.
 have Typed := types 995%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_995_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1003 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1003%nat final) = Some (Gtyp (global_type_at 1003%nat)).
Proof.
 have Typed := types 1003%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_1003_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::23] 4 final) = Some (Gtyp (global_type_at 1003%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_1007 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1007%nat final) = Some (Gtyp (global_type_at 1007%nat)).
Proof.
 have Typed := types 1007%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_1007_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::23] 5 final) = Some (Gtyp (global_type_at 1007%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_1010 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1010%nat final) = Some (Gtyp (global_type_at 1010%nat)).
Proof.
 have Typed := types 1010%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1010_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1013 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1013%nat final) = Some (Gtyp (global_type_at 1013%nat)).
Proof.
 have Typed := types 1013%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1013_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1021 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1021%nat final) = Some (Gtyp (global_type_at 1021%nat)).
Proof.
 have Typed := types 1021%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_1021_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::24] 4 final) = Some (Gtyp (global_type_at 1021%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_1025 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1025%nat final) = Some (Gtyp (global_type_at 1025%nat)).
Proof.
 have Typed := types 1025%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_1025_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::24] 5 final) = Some (Gtyp (global_type_at 1025%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_1028 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1028%nat final) = Some (Gtyp (global_type_at 1028%nat)).
Proof.
 have Typed := types 1028%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1028_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1031 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1031%nat final) = Some (Gtyp (global_type_at 1031%nat)).
Proof.
 have Typed := types 1031%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1031_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1039 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1039%nat final) = Some (Gtyp (global_type_at 1039%nat)).
Proof.
 have Typed := types 1039%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_1039_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::25] 4 final) = Some (Gtyp (global_type_at 1039%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_1043 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1043%nat final) = Some (Gtyp (global_type_at 1043%nat)).
Proof.
 have Typed := types 1043%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_1043_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::25] 5 final) = Some (Gtyp (global_type_at 1043%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_1046 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1046%nat final) = Some (Gtyp (global_type_at 1046%nat)).
Proof.
 have Typed := types 1046%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1046_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1049 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1049%nat final) = Some (Gtyp (global_type_at 1049%nat)).
Proof.
 have Typed := types 1049%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1049_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1057 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1057%nat final) = Some (Gtyp (global_type_at 1057%nat)).
Proof.
 have Typed := types 1057%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_1057_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::26] 4 final) = Some (Gtyp (global_type_at 1057%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_1061 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1061%nat final) = Some (Gtyp (global_type_at 1061%nat)).
Proof.
 have Typed := types 1061%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_1061_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::26] 5 final) = Some (Gtyp (global_type_at 1061%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_1064 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1064%nat final) = Some (Gtyp (global_type_at 1064%nat)).
Proof.
 have Typed := types 1064%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1064_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1067 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1067%nat final) = Some (Gtyp (global_type_at 1067%nat)).
Proof.
 have Typed := types 1067%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1067_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1070 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1070%nat final) = Some (Gtyp (global_type_at 1070%nat)).
Proof.
 have Typed := types 1070%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1070_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1081 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1081%nat final) = Some (Gtyp (global_type_at 1081%nat)).
Proof.
 have Typed := types 1081%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_1081_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::27] 5 final) = Some (Gtyp (global_type_at 1081%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_1085 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1085%nat final) = Some (Gtyp (global_type_at 1085%nat)).
Proof.
 have Typed := types 1085%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_1085_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::27] 6 final) = Some (Gtyp (global_type_at 1085%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_1088 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1088%nat final) = Some (Gtyp (global_type_at 1088%nat)).
Proof.
 have Typed := types 1088%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1088_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1091 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1091%nat final) = Some (Gtyp (global_type_at 1091%nat)).
Proof.
 have Typed := types 1091%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1091_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1094 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1094%nat final) = Some (Gtyp (global_type_at 1094%nat)).
Proof.
 have Typed := types 1094%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1094_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1105 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1105%nat final) = Some (Gtyp (global_type_at 1105%nat)).
Proof.
 have Typed := types 1105%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_1105_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::28] 5 final) = Some (Gtyp (global_type_at 1105%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_1109 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1109%nat final) = Some (Gtyp (global_type_at 1109%nat)).
Proof.
 have Typed := types 1109%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_1109_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::28] 6 final) = Some (Gtyp (global_type_at 1109%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_1112 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1112%nat final) = Some (Gtyp (global_type_at 1112%nat)).
Proof.
 have Typed := types 1112%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1112_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1115 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1115%nat final) = Some (Gtyp (global_type_at 1115%nat)).
Proof.
 have Typed := types 1115%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1115_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1123 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1123%nat final) = Some (Gtyp (global_type_at 1123%nat)).
Proof.
 have Typed := types 1123%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_1123_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::29] 4 final) = Some (Gtyp (global_type_at 1123%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_1127 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1127%nat final) = Some (Gtyp (global_type_at 1127%nat)).
Proof.
 have Typed := types 1127%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_1127_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::29] 5 final) = Some (Gtyp (global_type_at 1127%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_1130 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1130%nat final) = Some (Gtyp (global_type_at 1130%nat)).
Proof.
 have Typed := types 1130%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1130_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1133 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1133%nat final) = Some (Gtyp (global_type_at 1133%nat)).
Proof.
 have Typed := types 1133%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1133_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1141 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1141%nat final) = Some (Gtyp (global_type_at 1141%nat)).
Proof.
 have Typed := types 1141%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_1141_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::30] 4 final) = Some (Gtyp (global_type_at 1141%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_1145 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1145%nat final) = Some (Gtyp (global_type_at 1145%nat)).
Proof.
 have Typed := types 1145%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_1145_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::30] 5 final) = Some (Gtyp (global_type_at 1145%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_1148 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1148%nat final) = Some (Gtyp (global_type_at 1148%nat)).
Proof.
 have Typed := types 1148%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1148_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1151 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1151%nat final) = Some (Gtyp (global_type_at 1151%nat)).
Proof.
 have Typed := types 1151%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1151_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1159 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1159%nat final) = Some (Gtyp (global_type_at 1159%nat)).
Proof.
 have Typed := types 1159%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_1159_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::31] 4 final) = Some (Gtyp (global_type_at 1159%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_1163 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1163%nat final) = Some (Gtyp (global_type_at 1163%nat)).
Proof.
 have Typed := types 1163%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_1163_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::31] 5 final) = Some (Gtyp (global_type_at 1163%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_1166 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1166%nat final) = Some (Gtyp (global_type_at 1166%nat)).
Proof.
 have Typed := types 1166%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1166_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1169 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1169%nat final) = Some (Gtyp (global_type_at 1169%nat)).
Proof.
 have Typed := types 1169%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1169_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1177 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1177%nat final) = Some (Gtyp (global_type_at 1177%nat)).
Proof.
 have Typed := types 1177%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_1177_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::32] 4 final) = Some (Gtyp (global_type_at 1177%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_1181 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1181%nat final) = Some (Gtyp (global_type_at 1181%nat)).
Proof.
 have Typed := types 1181%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_1181_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::32] 5 final) = Some (Gtyp (global_type_at 1181%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_1184 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1184%nat final) = Some (Gtyp (global_type_at 1184%nat)).
Proof.
 have Typed := types 1184%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1184_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1187 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1187%nat final) = Some (Gtyp (global_type_at 1187%nat)).
Proof.
 have Typed := types 1187%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1187_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1190 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1190%nat final) = Some (Gtyp (global_type_at 1190%nat)).
Proof.
 have Typed := types 1190%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1190_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1201 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1201%nat final) = Some (Gtyp (global_type_at 1201%nat)).
Proof.
 have Typed := types 1201%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_1201_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::33] 5 final) = Some (Gtyp (global_type_at 1201%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_1205 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1205%nat final) = Some (Gtyp (global_type_at 1205%nat)).
Proof.
 have Typed := types 1205%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_1205_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::33] 6 final) = Some (Gtyp (global_type_at 1205%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_1208 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1208%nat final) = Some (Gtyp (global_type_at 1208%nat)).
Proof.
 have Typed := types 1208%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1208_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1211 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1211%nat final) = Some (Gtyp (global_type_at 1211%nat)).
Proof.
 have Typed := types 1211%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1211_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1219 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1219%nat final) = Some (Gtyp (global_type_at 1219%nat)).
Proof.
 have Typed := types 1219%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_1219_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::34] 4 final) = Some (Gtyp (global_type_at 1219%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_1223 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1223%nat final) = Some (Gtyp (global_type_at 1223%nat)).
Proof.
 have Typed := types 1223%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_1223_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::34] 5 final) = Some (Gtyp (global_type_at 1223%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_1226 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1226%nat final) = Some (Gtyp (global_type_at 1226%nat)).
Proof.
 have Typed := types 1226%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1226_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1229 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1229%nat final) = Some (Gtyp (global_type_at 1229%nat)).
Proof.
 have Typed := types 1229%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1229_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1237 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1237%nat final) = Some (Gtyp (global_type_at 1237%nat)).
Proof.
 have Typed := types 1237%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_1237_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::35] 4 final) = Some (Gtyp (global_type_at 1237%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_1241 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1241%nat final) = Some (Gtyp (global_type_at 1241%nat)).
Proof.
 have Typed := types 1241%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_1241_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::35] 5 final) = Some (Gtyp (global_type_at 1241%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_1244 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1244%nat final) = Some (Gtyp (global_type_at 1244%nat)).
Proof.
 have Typed := types 1244%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1244_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1247 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1247%nat final) = Some (Gtyp (global_type_at 1247%nat)).
Proof.
 have Typed := types 1247%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1247_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1255 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1255%nat final) = Some (Gtyp (global_type_at 1255%nat)).
Proof.
 have Typed := types 1255%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_1255_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::36] 4 final) = Some (Gtyp (global_type_at 1255%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_1259 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1259%nat final) = Some (Gtyp (global_type_at 1259%nat)).
Proof.
 have Typed := types 1259%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_1259_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::36] 5 final) = Some (Gtyp (global_type_at 1259%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_1299 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1299%nat final) = Some (Gtyp (global_type_at 1299%nat)).
Proof.
 have Typed := types 1299%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [value [Found ValueType]].
 destruct (global_scalar_1299_type invalid snapshot final value Found ValueType ran) as [result [Result ResultType]].
 change (option_map type_of_val (HierarchyFacts.circuit_lookup [::] 6 final) = Some (Gtyp (global_type_at 1299%nat))).
 rewrite Result. exact (f_equal Some ResultType).
Qed.
Lemma global_type_progress_1310 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1310%nat final) = Some (Gtyp (global_type_at 1310%nat)).
Proof.
 have Typed := types 1310%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1310_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1311 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1311%nat final) = Some (Gtyp (global_type_at 1311%nat)).
Proof.
 have Typed := types 1311%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1311_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1312 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1312%nat final) = Some (Gtyp (global_type_at 1312%nat)).
Proof.
 have Typed := types 1312%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1312_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1313 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1313%nat final) = Some (Gtyp (global_type_at 1313%nat)).
Proof.
 have Typed := types 1313%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1313_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1314 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1314%nat final) = Some (Gtyp (global_type_at 1314%nat)).
Proof.
 have Typed := types 1314%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1314_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1315 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1315%nat final) = Some (Gtyp (global_type_at 1315%nat)).
Proof.
 have Typed := types 1315%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1315_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1316 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1316%nat final) = Some (Gtyp (global_type_at 1316%nat)).
Proof.
 have Typed := types 1316%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1316_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1317 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1317%nat final) = Some (Gtyp (global_type_at 1317%nat)).
Proof.
 have Typed := types 1317%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1317_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1318 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1318%nat final) = Some (Gtyp (global_type_at 1318%nat)).
Proof.
 have Typed := types 1318%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1318_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1319 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1319%nat final) = Some (Gtyp (global_type_at 1319%nat)).
Proof.
 have Typed := types 1319%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1319_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1320 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1320%nat final) = Some (Gtyp (global_type_at 1320%nat)).
Proof.
 have Typed := types 1320%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1320_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1321 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1321%nat final) = Some (Gtyp (global_type_at 1321%nat)).
Proof.
 have Typed := types 1321%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1321_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1322 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1322%nat final) = Some (Gtyp (global_type_at 1322%nat)).
Proof.
 have Typed := types 1322%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1322_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1323 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1323%nat final) = Some (Gtyp (global_type_at 1323%nat)).
Proof.
 have Typed := types 1323%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1323_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1324 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1324%nat final) = Some (Gtyp (global_type_at 1324%nat)).
Proof.
 have Typed := types 1324%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1324_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1325 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1325%nat final) = Some (Gtyp (global_type_at 1325%nat)).
Proof.
 have Typed := types 1325%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1325_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1326 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1326%nat final) = Some (Gtyp (global_type_at 1326%nat)).
Proof.
 have Typed := types 1326%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1326_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1327 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1327%nat final) = Some (Gtyp (global_type_at 1327%nat)).
Proof.
 have Typed := types 1327%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1327_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1328 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1328%nat final) = Some (Gtyp (global_type_at 1328%nat)).
Proof.
 have Typed := types 1328%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1328_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1329 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1329%nat final) = Some (Gtyp (global_type_at 1329%nat)).
Proof.
 have Typed := types 1329%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1329_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1330 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1330%nat final) = Some (Gtyp (global_type_at 1330%nat)).
Proof.
 have Typed := types 1330%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1330_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1331 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1331%nat final) = Some (Gtyp (global_type_at 1331%nat)).
Proof.
 have Typed := types 1331%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1331_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1332 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1332%nat final) = Some (Gtyp (global_type_at 1332%nat)).
Proof.
 have Typed := types 1332%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1332_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1333 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1333%nat final) = Some (Gtyp (global_type_at 1333%nat)).
Proof.
 have Typed := types 1333%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1333_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1334 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1334%nat final) = Some (Gtyp (global_type_at 1334%nat)).
Proof.
 have Typed := types 1334%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1334_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1335 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1335%nat final) = Some (Gtyp (global_type_at 1335%nat)).
Proof.
 have Typed := types 1335%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1335_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1336 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1336%nat final) = Some (Gtyp (global_type_at 1336%nat)).
Proof.
 have Typed := types 1336%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1336_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1337 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1337%nat final) = Some (Gtyp (global_type_at 1337%nat)).
Proof.
 have Typed := types 1337%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1337_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1338 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1338%nat final) = Some (Gtyp (global_type_at 1338%nat)).
Proof.
 have Typed := types 1338%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1338_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1339 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1339%nat final) = Some (Gtyp (global_type_at 1339%nat)).
Proof.
 have Typed := types 1339%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1339_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1340 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1340%nat final) = Some (Gtyp (global_type_at 1340%nat)).
Proof.
 have Typed := types 1340%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1340_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1341 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1341%nat final) = Some (Gtyp (global_type_at 1341%nat)).
Proof.
 have Typed := types 1341%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1341_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1342 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1342%nat final) = Some (Gtyp (global_type_at 1342%nat)).
Proof.
 have Typed := types 1342%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1342_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1343 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1343%nat final) = Some (Gtyp (global_type_at 1343%nat)).
Proof.
 have Typed := types 1343%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1343_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1344 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1344%nat final) = Some (Gtyp (global_type_at 1344%nat)).
Proof.
 have Typed := types 1344%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1344_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1345 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1345%nat final) = Some (Gtyp (global_type_at 1345%nat)).
Proof.
 have Typed := types 1345%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1345_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1346 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1346%nat final) = Some (Gtyp (global_type_at 1346%nat)).
Proof.
 have Typed := types 1346%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1346_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1347 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1347%nat final) = Some (Gtyp (global_type_at 1347%nat)).
Proof.
 have Typed := types 1347%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1347_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1348 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1348%nat final) = Some (Gtyp (global_type_at 1348%nat)).
Proof.
 have Typed := types 1348%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1348_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1349 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1349%nat final) = Some (Gtyp (global_type_at 1349%nat)).
Proof.
 have Typed := types 1349%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1349_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1350 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1350%nat final) = Some (Gtyp (global_type_at 1350%nat)).
Proof.
 have Typed := types 1350%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1350_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1351 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1351%nat final) = Some (Gtyp (global_type_at 1351%nat)).
Proof.
 have Typed := types 1351%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1351_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1352 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1352%nat final) = Some (Gtyp (global_type_at 1352%nat)).
Proof.
 have Typed := types 1352%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1352_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1353 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1353%nat final) = Some (Gtyp (global_type_at 1353%nat)).
Proof.
 have Typed := types 1353%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1353_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1354 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1354%nat final) = Some (Gtyp (global_type_at 1354%nat)).
Proof.
 have Typed := types 1354%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1354_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1355 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1355%nat final) = Some (Gtyp (global_type_at 1355%nat)).
Proof.
 have Typed := types 1355%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1355_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1356 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1356%nat final) = Some (Gtyp (global_type_at 1356%nat)).
Proof.
 have Typed := types 1356%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1356_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1357 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1357%nat final) = Some (Gtyp (global_type_at 1357%nat)).
Proof.
 have Typed := types 1357%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1357_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1358 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1358%nat final) = Some (Gtyp (global_type_at 1358%nat)).
Proof.
 have Typed := types 1358%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1358_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1359 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1359%nat final) = Some (Gtyp (global_type_at 1359%nat)).
Proof.
 have Typed := types 1359%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1359_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1360 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1360%nat final) = Some (Gtyp (global_type_at 1360%nat)).
Proof.
 have Typed := types 1360%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1360_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1361 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1361%nat final) = Some (Gtyp (global_type_at 1361%nat)).
Proof.
 have Typed := types 1361%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1361_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1362 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1362%nat final) = Some (Gtyp (global_type_at 1362%nat)).
Proof.
 have Typed := types 1362%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1362_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1363 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1363%nat final) = Some (Gtyp (global_type_at 1363%nat)).
Proof.
 have Typed := types 1363%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1363_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1364 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1364%nat final) = Some (Gtyp (global_type_at 1364%nat)).
Proof.
 have Typed := types 1364%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1364_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1365 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1365%nat final) = Some (Gtyp (global_type_at 1365%nat)).
Proof.
 have Typed := types 1365%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1365_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1366 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1366%nat final) = Some (Gtyp (global_type_at 1366%nat)).
Proof.
 have Typed := types 1366%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1366_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1367 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1367%nat final) = Some (Gtyp (global_type_at 1367%nat)).
Proof.
 have Typed := types 1367%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1367_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1368 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1368%nat final) = Some (Gtyp (global_type_at 1368%nat)).
Proof.
 have Typed := types 1368%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1368_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1369 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1369%nat final) = Some (Gtyp (global_type_at 1369%nat)).
Proof.
 have Typed := types 1369%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1369_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1464 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1464%nat final) = Some (Gtyp (global_type_at 1464%nat)).
Proof.
 have Typed := types 1464%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1464_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1465 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1465%nat final) = Some (Gtyp (global_type_at 1465%nat)).
Proof.
 have Typed := types 1465%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1465_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1466 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1466%nat final) = Some (Gtyp (global_type_at 1466%nat)).
Proof.
 have Typed := types 1466%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1466_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1467 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1467%nat final) = Some (Gtyp (global_type_at 1467%nat)).
Proof.
 have Typed := types 1467%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1467_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1532 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1532%nat final) = Some (Gtyp (global_type_at 1532%nat)).
Proof.
 have Typed := types 1532%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1532_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1533 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1533%nat final) = Some (Gtyp (global_type_at 1533%nat)).
Proof.
 have Typed := types 1533%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1533_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1534 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1534%nat final) = Some (Gtyp (global_type_at 1534%nat)).
Proof.
 have Typed := types 1534%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1534_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1535 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1535%nat final) = Some (Gtyp (global_type_at 1535%nat)).
Proof.
 have Typed := types 1535%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1535_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1600 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1600%nat final) = Some (Gtyp (global_type_at 1600%nat)).
Proof.
 have Typed := types 1600%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1600_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1601 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1601%nat final) = Some (Gtyp (global_type_at 1601%nat)).
Proof.
 have Typed := types 1601%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1601_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1602 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1602%nat final) = Some (Gtyp (global_type_at 1602%nat)).
Proof.
 have Typed := types 1602%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1602_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1603 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1603%nat final) = Some (Gtyp (global_type_at 1603%nat)).
Proof.
 have Typed := types 1603%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1603_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1668 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1668%nat final) = Some (Gtyp (global_type_at 1668%nat)).
Proof.
 have Typed := types 1668%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1668_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1669 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1669%nat final) = Some (Gtyp (global_type_at 1669%nat)).
Proof.
 have Typed := types 1669%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1669_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1670 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1670%nat final) = Some (Gtyp (global_type_at 1670%nat)).
Proof.
 have Typed := types 1670%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1670_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1671 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1671%nat final) = Some (Gtyp (global_type_at 1671%nat)).
Proof.
 have Typed := types 1671%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1671_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1736 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1736%nat final) = Some (Gtyp (global_type_at 1736%nat)).
Proof.
 have Typed := types 1736%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1736_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1737 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1737%nat final) = Some (Gtyp (global_type_at 1737%nat)).
Proof.
 have Typed := types 1737%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1737_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1738 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1738%nat final) = Some (Gtyp (global_type_at 1738%nat)).
Proof.
 have Typed := types 1738%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1738_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1739 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1739%nat final) = Some (Gtyp (global_type_at 1739%nat)).
Proof.
 have Typed := types 1739%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1739_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1804 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1804%nat final) = Some (Gtyp (global_type_at 1804%nat)).
Proof.
 have Typed := types 1804%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1804_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1805 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1805%nat final) = Some (Gtyp (global_type_at 1805%nat)).
Proof.
 have Typed := types 1805%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1805_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1806 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1806%nat final) = Some (Gtyp (global_type_at 1806%nat)).
Proof.
 have Typed := types 1806%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1806_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1807 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1807%nat final) = Some (Gtyp (global_type_at 1807%nat)).
Proof.
 have Typed := types 1807%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1807_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1872 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1872%nat final) = Some (Gtyp (global_type_at 1872%nat)).
Proof.
 have Typed := types 1872%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1872_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1873 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1873%nat final) = Some (Gtyp (global_type_at 1873%nat)).
Proof.
 have Typed := types 1873%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1873_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1874 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1874%nat final) = Some (Gtyp (global_type_at 1874%nat)).
Proof.
 have Typed := types 1874%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1874_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1875 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1875%nat final) = Some (Gtyp (global_type_at 1875%nat)).
Proof.
 have Typed := types 1875%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1875_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1940 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1940%nat final) = Some (Gtyp (global_type_at 1940%nat)).
Proof.
 have Typed := types 1940%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1940_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1941 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1941%nat final) = Some (Gtyp (global_type_at 1941%nat)).
Proof.
 have Typed := types 1941%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1941_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1942 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1942%nat final) = Some (Gtyp (global_type_at 1942%nat)).
Proof.
 have Typed := types 1942%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1942_type invalid snapshot final Typed ran).
Qed.
Lemma global_type_progress_1943 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 option_map type_of_val (global_value_at 1943%nat final) = Some (Gtyp (global_type_at 1943%nat)).
Proof.
 have Typed := types 1943%nat (ltac:(lia)) (Logic.eq_refl true).
 exact (global_field_1943_type invalid snapshot final Typed ran).
Qed.
