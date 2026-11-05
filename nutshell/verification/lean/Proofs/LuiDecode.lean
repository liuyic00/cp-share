import Proofs.DecodeBits
namespace NutShellProofs
open nNutCore

theorem lui_source_select_0 (s : State) (i : Inputs)
    (lui : BitVec.extractLsb' 0 7 (v26210 s i) = 55) : v28006 s i = 1 := by
  have hv26389 : v26389 s i = 0 := by
    have miss : v26386 s i ≠ v26388 s i := by
      intro matched
      have op := opcode_of_mask (v26210 s i) (v26387 s i) (v26386 s i) (by unfold v26387; decide) matched
      have val : BitVec.extractLsb' 0 7 (v26386 s i) = 19 := by unfold v26386; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 19) op
    rw [v26389, if_neg miss]
  have hv26394 : v26394 s i = 0 := by
    have miss : v26391 s i ≠ v26393 s i := by
      intro matched
      have op := opcode_of_mask (v26210 s i) (v26392 s i) (v26391 s i) (by unfold v26392; decide) matched
      have val : BitVec.extractLsb' 0 7 (v26391 s i) = 19 := by unfold v26391; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 19) op
    rw [v26394, if_neg miss]
  have hv26399 : v26399 s i = 0 := by
    have miss : v26396 s i ≠ v26398 s i := by
      intro matched
      have op := opcode_of_mask (v26210 s i) (v26397 s i) (v26396 s i) (by unfold v26397; decide) matched
      have val : BitVec.extractLsb' 0 7 (v26396 s i) = 19 := by unfold v26396; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 19) op
    rw [v26399, if_neg miss]
  have hv26404 : v26404 s i = 0 := by
    have miss : v26401 s i ≠ v26403 s i := by
      intro matched
      have op := opcode_of_mask (v26210 s i) (v26402 s i) (v26401 s i) (by unfold v26402; decide) matched
      have val : BitVec.extractLsb' 0 7 (v26401 s i) = 19 := by unfold v26401; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 19) op
    rw [v26404, if_neg miss]
  have hv26409 : v26409 s i = 0 := by
    have miss : v26406 s i ≠ v26408 s i := by
      intro matched
      have op := opcode_of_mask (v26210 s i) (v26407 s i) (v26406 s i) (by unfold v26407; decide) matched
      have val : BitVec.extractLsb' 0 7 (v26406 s i) = 19 := by unfold v26406; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 19) op
    rw [v26409, if_neg miss]
  have hv26414 : v26414 s i = 0 := by
    have miss : v26411 s i ≠ v26413 s i := by
      intro matched
      have op := opcode_of_mask (v26210 s i) (v26412 s i) (v26411 s i) (by unfold v26412; decide) matched
      have val : BitVec.extractLsb' 0 7 (v26411 s i) = 19 := by unfold v26411; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 19) op
    rw [v26414, if_neg miss]
  have hv26419 : v26419 s i = 0 := by
    have miss : v26416 s i ≠ v26418 s i := by
      intro matched
      have op := opcode_of_mask (v26210 s i) (v26417 s i) (v26416 s i) (by unfold v26417; decide) matched
      have val : BitVec.extractLsb' 0 7 (v26416 s i) = 19 := by unfold v26416; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 19) op
    rw [v26419, if_neg miss]
  have hv26424 : v26424 s i = 0 := by
    have miss : v26421 s i ≠ v26423 s i := by
      intro matched
      have op := opcode_of_mask (v26210 s i) (v26422 s i) (v26421 s i) (by unfold v26422; decide) matched
      have val : BitVec.extractLsb' 0 7 (v26421 s i) = 19 := by unfold v26421; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 19) op
    rw [v26424, if_neg miss]
  have hv26429 : v26429 s i = 0 := by
    have miss : v26426 s i ≠ v26428 s i := by
      intro matched
      have op := opcode_of_mask (v26210 s i) (v26427 s i) (v26426 s i) (by unfold v26427; decide) matched
      have val : BitVec.extractLsb' 0 7 (v26426 s i) = 19 := by unfold v26426; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 19) op
    rw [v26429, if_neg miss]
  have hv26434 : v26434 s i = 0 := by
    have miss : v26431 s i ≠ v26433 s i := by
      intro matched
      have op := opcode_of_mask (v26210 s i) (v26432 s i) (v26431 s i) (by unfold v26432; decide) matched
      have val : BitVec.extractLsb' 0 7 (v26431 s i) = 51 := by unfold v26431; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v26434, if_neg miss]
  have hv26439 : v26439 s i = 0 := by
    have miss : v26436 s i ≠ v26438 s i := by
      intro matched
      have op := opcode_of_mask (v26210 s i) (v26437 s i) (v26436 s i) (by unfold v26437; decide) matched
      have val : BitVec.extractLsb' 0 7 (v26436 s i) = 51 := by unfold v26436; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v26439, if_neg miss]
  have hv26444 : v26444 s i = 0 := by
    have miss : v26441 s i ≠ v26443 s i := by
      intro matched
      have op := opcode_of_mask (v26210 s i) (v26442 s i) (v26441 s i) (by unfold v26442; decide) matched
      have val : BitVec.extractLsb' 0 7 (v26441 s i) = 51 := by unfold v26441; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v26444, if_neg miss]
  have hv26449 : v26449 s i = 0 := by
    have miss : v26446 s i ≠ v26448 s i := by
      intro matched
      have op := opcode_of_mask (v26210 s i) (v26447 s i) (v26446 s i) (by unfold v26447; decide) matched
      have val : BitVec.extractLsb' 0 7 (v26446 s i) = 51 := by unfold v26446; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v26449, if_neg miss]
  have hv26454 : v26454 s i = 0 := by
    have miss : v26451 s i ≠ v26453 s i := by
      intro matched
      have op := opcode_of_mask (v26210 s i) (v26452 s i) (v26451 s i) (by unfold v26452; decide) matched
      have val : BitVec.extractLsb' 0 7 (v26451 s i) = 51 := by unfold v26451; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v26454, if_neg miss]
  have hv26459 : v26459 s i = 0 := by
    have miss : v26456 s i ≠ v26458 s i := by
      intro matched
      have op := opcode_of_mask (v26210 s i) (v26457 s i) (v26456 s i) (by unfold v26457; decide) matched
      have val : BitVec.extractLsb' 0 7 (v26456 s i) = 51 := by unfold v26456; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v26459, if_neg miss]
  have hv26464 : v26464 s i = 0 := by
    have miss : v26461 s i ≠ v26463 s i := by
      intro matched
      have op := opcode_of_mask (v26210 s i) (v26462 s i) (v26461 s i) (by unfold v26462; decide) matched
      have val : BitVec.extractLsb' 0 7 (v26461 s i) = 51 := by unfold v26461; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v26464, if_neg miss]
  have hv26469 : v26469 s i = 0 := by
    have miss : v26466 s i ≠ v26468 s i := by
      intro matched
      have op := opcode_of_mask (v26210 s i) (v26467 s i) (v26466 s i) (by unfold v26467; decide) matched
      have val : BitVec.extractLsb' 0 7 (v26466 s i) = 51 := by unfold v26466; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v26469, if_neg miss]
  have hv26474 : v26474 s i = 0 := by
    have miss : v26471 s i ≠ v26473 s i := by
      intro matched
      have op := opcode_of_mask (v26210 s i) (v26472 s i) (v26471 s i) (by unfold v26472; decide) matched
      have val : BitVec.extractLsb' 0 7 (v26471 s i) = 51 := by unfold v26471; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v26474, if_neg miss]
  have hv26479 : v26479 s i = 0 := by
    have miss : v26476 s i ≠ v26478 s i := by
      intro matched
      have op := opcode_of_mask (v26210 s i) (v26477 s i) (v26476 s i) (by unfold v26477; decide) matched
      have val : BitVec.extractLsb' 0 7 (v26476 s i) = 51 := by unfold v26476; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v26479, if_neg miss]
  have hv26484 : v26484 s i = 0 := by
    have miss : v26481 s i ≠ v26483 s i := by
      intro matched
      have op := opcode_of_mask (v26210 s i) (v26482 s i) (v26481 s i) (by unfold v26482; decide) matched
      have val : BitVec.extractLsb' 0 7 (v26481 s i) = 23 := by unfold v26481; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 23) op
    rw [v26484, if_neg miss]
  have hv26489 : v26489 s i = 1 := by
    have eq := low_opcode_mask (v26210 s i) (55 : BitVec 7) lui
    change v26486 s i = v26488 s i at eq
    rw [v26489, if_pos eq]
  rcases BitVec.eq_zero_or_eq_one (v26384 s i) with h | h
  all_goals simp [v28006, v28003, v28000, v27999, v28002, v28001, v28005, v28004, v26897, v26385, v26896, v26390, v26895, v26395, v26894, v26400, v26893, v26405, v26892, v26410, v26891, v26415, v26890, v26420, v26889, v26425, v26888, v26430, v26887, v26435, v26886, v26440, v26885, v26445, v26884, v26450, v26883, v26455, v26882, v26460, v26881, v26465, v26880, v26470, v26879, v26475, v26878, v26480, v26877, v26485, v26876, v26490, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, h]
#print axioms lui_source_select_0

theorem lui_source_select_1 (s : State) (i : Inputs)
    (lui : BitVec.extractLsb' 0 7 (v26223 s i) = 55) : v28023 s i = 1 := by
  have hv26916 : v26916 s i = 0 := by
    have miss : v26913 s i ≠ v26915 s i := by
      intro matched
      have op := opcode_of_mask (v26223 s i) (v26914 s i) (v26913 s i) (by unfold v26914; decide) matched
      have val : BitVec.extractLsb' 0 7 (v26913 s i) = 19 := by unfold v26913; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 19) op
    rw [v26916, if_neg miss]
  have hv26921 : v26921 s i = 0 := by
    have miss : v26918 s i ≠ v26920 s i := by
      intro matched
      have op := opcode_of_mask (v26223 s i) (v26919 s i) (v26918 s i) (by unfold v26919; decide) matched
      have val : BitVec.extractLsb' 0 7 (v26918 s i) = 19 := by unfold v26918; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 19) op
    rw [v26921, if_neg miss]
  have hv26926 : v26926 s i = 0 := by
    have miss : v26923 s i ≠ v26925 s i := by
      intro matched
      have op := opcode_of_mask (v26223 s i) (v26924 s i) (v26923 s i) (by unfold v26924; decide) matched
      have val : BitVec.extractLsb' 0 7 (v26923 s i) = 19 := by unfold v26923; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 19) op
    rw [v26926, if_neg miss]
  have hv26931 : v26931 s i = 0 := by
    have miss : v26928 s i ≠ v26930 s i := by
      intro matched
      have op := opcode_of_mask (v26223 s i) (v26929 s i) (v26928 s i) (by unfold v26929; decide) matched
      have val : BitVec.extractLsb' 0 7 (v26928 s i) = 19 := by unfold v26928; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 19) op
    rw [v26931, if_neg miss]
  have hv26936 : v26936 s i = 0 := by
    have miss : v26933 s i ≠ v26935 s i := by
      intro matched
      have op := opcode_of_mask (v26223 s i) (v26934 s i) (v26933 s i) (by unfold v26934; decide) matched
      have val : BitVec.extractLsb' 0 7 (v26933 s i) = 19 := by unfold v26933; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 19) op
    rw [v26936, if_neg miss]
  have hv26941 : v26941 s i = 0 := by
    have miss : v26938 s i ≠ v26940 s i := by
      intro matched
      have op := opcode_of_mask (v26223 s i) (v26939 s i) (v26938 s i) (by unfold v26939; decide) matched
      have val : BitVec.extractLsb' 0 7 (v26938 s i) = 19 := by unfold v26938; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 19) op
    rw [v26941, if_neg miss]
  have hv26946 : v26946 s i = 0 := by
    have miss : v26943 s i ≠ v26945 s i := by
      intro matched
      have op := opcode_of_mask (v26223 s i) (v26944 s i) (v26943 s i) (by unfold v26944; decide) matched
      have val : BitVec.extractLsb' 0 7 (v26943 s i) = 19 := by unfold v26943; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 19) op
    rw [v26946, if_neg miss]
  have hv26951 : v26951 s i = 0 := by
    have miss : v26948 s i ≠ v26950 s i := by
      intro matched
      have op := opcode_of_mask (v26223 s i) (v26949 s i) (v26948 s i) (by unfold v26949; decide) matched
      have val : BitVec.extractLsb' 0 7 (v26948 s i) = 19 := by unfold v26948; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 19) op
    rw [v26951, if_neg miss]
  have hv26956 : v26956 s i = 0 := by
    have miss : v26953 s i ≠ v26955 s i := by
      intro matched
      have op := opcode_of_mask (v26223 s i) (v26954 s i) (v26953 s i) (by unfold v26954; decide) matched
      have val : BitVec.extractLsb' 0 7 (v26953 s i) = 19 := by unfold v26953; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 19) op
    rw [v26956, if_neg miss]
  have hv26961 : v26961 s i = 0 := by
    have miss : v26958 s i ≠ v26960 s i := by
      intro matched
      have op := opcode_of_mask (v26223 s i) (v26959 s i) (v26958 s i) (by unfold v26959; decide) matched
      have val : BitVec.extractLsb' 0 7 (v26958 s i) = 51 := by unfold v26958; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v26961, if_neg miss]
  have hv26966 : v26966 s i = 0 := by
    have miss : v26963 s i ≠ v26965 s i := by
      intro matched
      have op := opcode_of_mask (v26223 s i) (v26964 s i) (v26963 s i) (by unfold v26964; decide) matched
      have val : BitVec.extractLsb' 0 7 (v26963 s i) = 51 := by unfold v26963; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v26966, if_neg miss]
  have hv26971 : v26971 s i = 0 := by
    have miss : v26968 s i ≠ v26970 s i := by
      intro matched
      have op := opcode_of_mask (v26223 s i) (v26969 s i) (v26968 s i) (by unfold v26969; decide) matched
      have val : BitVec.extractLsb' 0 7 (v26968 s i) = 51 := by unfold v26968; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v26971, if_neg miss]
  have hv26976 : v26976 s i = 0 := by
    have miss : v26973 s i ≠ v26975 s i := by
      intro matched
      have op := opcode_of_mask (v26223 s i) (v26974 s i) (v26973 s i) (by unfold v26974; decide) matched
      have val : BitVec.extractLsb' 0 7 (v26973 s i) = 51 := by unfold v26973; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v26976, if_neg miss]
  have hv26981 : v26981 s i = 0 := by
    have miss : v26978 s i ≠ v26980 s i := by
      intro matched
      have op := opcode_of_mask (v26223 s i) (v26979 s i) (v26978 s i) (by unfold v26979; decide) matched
      have val : BitVec.extractLsb' 0 7 (v26978 s i) = 51 := by unfold v26978; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v26981, if_neg miss]
  have hv26986 : v26986 s i = 0 := by
    have miss : v26983 s i ≠ v26985 s i := by
      intro matched
      have op := opcode_of_mask (v26223 s i) (v26984 s i) (v26983 s i) (by unfold v26984; decide) matched
      have val : BitVec.extractLsb' 0 7 (v26983 s i) = 51 := by unfold v26983; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v26986, if_neg miss]
  have hv26991 : v26991 s i = 0 := by
    have miss : v26988 s i ≠ v26990 s i := by
      intro matched
      have op := opcode_of_mask (v26223 s i) (v26989 s i) (v26988 s i) (by unfold v26989; decide) matched
      have val : BitVec.extractLsb' 0 7 (v26988 s i) = 51 := by unfold v26988; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v26991, if_neg miss]
  have hv26996 : v26996 s i = 0 := by
    have miss : v26993 s i ≠ v26995 s i := by
      intro matched
      have op := opcode_of_mask (v26223 s i) (v26994 s i) (v26993 s i) (by unfold v26994; decide) matched
      have val : BitVec.extractLsb' 0 7 (v26993 s i) = 51 := by unfold v26993; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v26996, if_neg miss]
  have hv27001 : v27001 s i = 0 := by
    have miss : v26998 s i ≠ v27000 s i := by
      intro matched
      have op := opcode_of_mask (v26223 s i) (v26999 s i) (v26998 s i) (by unfold v26999; decide) matched
      have val : BitVec.extractLsb' 0 7 (v26998 s i) = 51 := by unfold v26998; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v27001, if_neg miss]
  have hv27006 : v27006 s i = 0 := by
    have miss : v27003 s i ≠ v27005 s i := by
      intro matched
      have op := opcode_of_mask (v26223 s i) (v27004 s i) (v27003 s i) (by unfold v27004; decide) matched
      have val : BitVec.extractLsb' 0 7 (v27003 s i) = 51 := by unfold v27003; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v27006, if_neg miss]
  have hv27011 : v27011 s i = 0 := by
    have miss : v27008 s i ≠ v27010 s i := by
      intro matched
      have op := opcode_of_mask (v26223 s i) (v27009 s i) (v27008 s i) (by unfold v27009; decide) matched
      have val : BitVec.extractLsb' 0 7 (v27008 s i) = 23 := by unfold v27008; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 23) op
    rw [v27011, if_neg miss]
  have hv27016 : v27016 s i = 1 := by
    have eq := low_opcode_mask (v26223 s i) (55 : BitVec 7) lui
    change v27013 s i = v27015 s i at eq
    rw [v27016, if_pos eq]
  rcases BitVec.eq_zero_or_eq_one (v26911 s i) with h | h
  all_goals simp [v28023, v28020, v28017, v28016, v28019, v28018, v28022, v28021, v27424, v26912, v27423, v26917, v27422, v26922, v27421, v26927, v27420, v26932, v27419, v26937, v27418, v26942, v27417, v26947, v27416, v26952, v27415, v26957, v27414, v26962, v27413, v26967, v27412, v26972, v27411, v26977, v27410, v26982, v27409, v26987, v27408, v26992, v27407, v26997, v27406, v27002, v27405, v27007, v27404, v27012, v27403, v27017, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, h]
#print axioms lui_source_select_1
end NutShellProofs
