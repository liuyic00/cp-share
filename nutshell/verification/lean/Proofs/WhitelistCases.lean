import Proofs.WhitelistPipeline
namespace NutShellProofs
open nNutCore
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

theorem bit_or_one_iff (a b : BitVec 1) : a ||| b = 1 ↔ a = 1 ∨ b = 1 := by
  rcases BitVec.eq_zero_or_eq_one a with ha | ha <;>
    rcases BitVec.eq_zero_or_eq_one b with hb | hb <;> simp [ha, hb]

def WhitelistCases (instr : BitVec 64) : Prop :=
  ((((((((((((((((((((19 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 28799) ∨
    ((8211 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 28799)) ∨
    ((12307 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 28799)) ∨
    ((28691 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 28799)) ∨
    ((24595 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 28799)) ∨
    ((16403 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 28799)) ∨
    ((4115 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 4227887231)) ∨
    ((20499 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 4227887231)) ∨
    ((1073762323 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 4227887231)) ∨
    ((55 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 127)) ∨
    ((23 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 127)) ∨
    ((27 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 28799)) ∨
    ((4123 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 4261441663)) ∨
    ((20507 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 4261441663)) ∨
    ((20507 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 4261441663)) ∨
    ((1073762331 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 4261441663)) ∨
    ((((((((((((3 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 28799) ∨
    ((4099 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 28799)) ∨
    ((8195 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 28799)) ∨
    ((16387 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 28799)) ∨
    ((20483 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 28799)) ∨
    ((35 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 28799)) ∨
    ((4131 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 28799)) ∨
    ((8227 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 28799)) ∨
    ((24579 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 28799)) ∨
    ((12291 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 28799)) ∨
    ((12323 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 28799))) ∨
    (((((((((((51 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 4261441663) ∨
    ((8243 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 4261441663)) ∨
    ((12339 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 4261441663)) ∨
    ((28723 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 4261441663)) ∨
    ((24627 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 4261441663)) ∨
    ((16435 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 4261441663)) ∨
    ((4147 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 4261441663)) ∨
    ((20531 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 4261441663)) ∨
    ((1073741875 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 4261441663)) ∨
    ((1073762355 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 4261441663))) ∨
    (((((((((111 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 127) ∨
    ((103 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 28799)) ∨
    ((99 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 28799)) ∨
    ((4195 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 28799)) ∨
    ((16483 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 28799)) ∨
    ((24675 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 28799)) ∨
    ((20579 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 28799)) ∨
    ((28771 : BitVec 32) = BitVec.extractLsb' 0 32 instr &&& 28799)))

theorem allowed_instruction_cases (instr : BitVec 64) :
    AllowedInstruction instr ↔ WhitelistCases instr := by
  simp only [AllowedInstruction, WhitelistCases, whitelistEncoding.v30883, whitelistEncoding.v30885, whitelistEncoding.v30886, whitelistEncoding.v30887, whitelistEncoding.v30888, whitelistEncoding.v30889, whitelistEncoding.v30890, whitelistEncoding.v30891, whitelistEncoding.v30892, whitelistEncoding.v30893, whitelistEncoding.v30894, whitelistEncoding.v30895, whitelistEncoding.v30896, whitelistEncoding.v30897, whitelistEncoding.v30898, whitelistEncoding.v30899, whitelistEncoding.v30900, whitelistEncoding.v30901, whitelistEncoding.v30902, whitelistEncoding.v30903, whitelistEncoding.v30904, whitelistEncoding.v30905, whitelistEncoding.v30906, whitelistEncoding.v30907, whitelistEncoding.v30908, whitelistEncoding.v30909, whitelistEncoding.v30910, whitelistEncoding.v30911, whitelistEncoding.v30912, whitelistEncoding.v30913, whitelistEncoding.v14809, whitelistEncoding.v30914, whitelistEncoding.v30915, whitelistEncoding.v30916, whitelistEncoding.v30917, whitelistEncoding.v30918, whitelistEncoding.v30919, whitelistEncoding.v30920, whitelistEncoding.v30921, whitelistEncoding.v30922, whitelistEncoding.v30923, whitelistEncoding.v30924, whitelistEncoding.v30925, whitelistEncoding.v30926, whitelistEncoding.v30927, whitelistEncoding.v30928, whitelistEncoding.v30929, whitelistEncoding.v30930, whitelistEncoding.v30931, whitelistEncoding.v30932, whitelistEncoding.v30933, whitelistEncoding.v30934, whitelistEncoding.v30935, whitelistEncoding.v30936, whitelistEncoding.v30937, whitelistEncoding.v30938, whitelistEncoding.v30939, whitelistEncoding.v30940, whitelistEncoding.v14576, whitelistEncoding.v30941, whitelistEncoding.v30942, whitelistEncoding.v30943, whitelistEncoding.v30944, whitelistEncoding.v30945, whitelistEncoding.v30946, whitelistEncoding.v30947, whitelistEncoding.v30948, whitelistEncoding.v30949, whitelistEncoding.v30950, whitelistEncoding.v30951, whitelistEncoding.v30952, whitelistEncoding.v30953, whitelistEncoding.v30954, whitelistEncoding.v30955, whitelistEncoding.v30956, whitelistEncoding.v30957, whitelistEncoding.v30958, whitelistEncoding.v30959, whitelistEncoding.v30960, whitelistEncoding.v30961, whitelistEncoding.v30962, whitelistEncoding.v30963, whitelistEncoding.v30964, whitelistEncoding.v30965, whitelistEncoding.v30966, whitelistEncoding.v30967, whitelistEncoding.v30968, whitelistEncoding.v30969, whitelistEncoding.v30970, whitelistEncoding.v30971, whitelistEncoding.v30972, whitelistEncoding.v30973, whitelistEncoding.v30974, whitelistEncoding.v30975, whitelistEncoding.v30976, whitelistEncoding.v30977, whitelistEncoding.v30978, whitelistEncoding.v30979, whitelistEncoding.v30980, whitelistEncoding.v30981, whitelistEncoding.v30982, whitelistEncoding.v30983, whitelistEncoding.v30984, whitelistEncoding.v30985, whitelistEncoding.v30986, whitelistEncoding.v30987, whitelistEncoding.v30988, whitelistEncoding.v30989, whitelistEncoding.v30990, whitelistEncoding.v30991, whitelistEncoding.v30992, whitelistEncoding.v30993, whitelistEncoding.v30994, whitelistEncoding.v30995, whitelistEncoding.v30996, whitelistEncoding.v30997, whitelistEncoding.v30998, whitelistEncoding.v30999, whitelistEncoding.v31000, whitelistEncoding.v31001, whitelistEncoding.v31002, whitelistEncoding.v31003, whitelistEncoding.v31004, whitelistEncoding.v31005, whitelistEncoding.v31006, whitelistEncoding.v31007, whitelistEncoding.v31008, whitelistEncoding.v31009, whitelistEncoding.v31010, whitelistEncoding.v31011, whitelistEncoding.v31012, whitelistEncoding.v31013, whitelistEncoding.v31014, whitelistEncoding.v31015, whitelistEncoding.v31016, whitelistEncoding.v31017, whitelistEncoding.v31018, whitelistEncoding.v31019, whitelistEncoding.v31020, whitelistEncoding.v31021, whitelistEncoding.v31022, whitelistEncoding.v31023, whitelistEncoding.v31024, whitelistEncoding.v31025, whitelistEncoding.v31026, whitelistEncoding.v31027, whitelistEncoding.v31028, whitelistEncoding.v31029, whitelistEncoding.v31030, whitelistEncoding.v31031, whitelistEncoding.v31032, whitelistEncoding.v31033, whitelistEncoding.v31034, whitelistEncoding.v31035, whitelistEncoding.v31036, whitelistEncoding.v31037, whitelistEncoding.v31038, whitelistEncoding.v31039, whitelistEncoding.v31040, whitelistEncoding.v31041, whitelistEncoding.v31042, whitelistEncoding.v31043, whitelistEncoding.v31044, whitelistEncoding.v31045, whitelistEncoding.v31046, whitelistEncoding.v31047, whitelistEncoding.v31048, whitelistEncoding.v31049, whitelistEncoding.v31050, whitelistEncoding.v31051, whitelistEncoding.v31052, whitelistEncoding.v31053, whitelistEncoding.v31054, whitelistEncoding.v31055, whitelistEncoding.v31056, whitelistEncoding.v31057, whitelistEncoding.v31058, whitelistEncoding.v31059, whitelistEncoding.v31060, whitelistEncoding.v31061, whitelistEncoding.v31062, whitelistEncoding.v31063, whitelistEncoding.v31064, whitelistEncoding.v31065, whitelistEncoding.v31066, whitelistEncoding.v31067, whitelistEncoding.v31068, whitelistEncoding.v31069, whitelistEncoding.v31070, whitelistEncoding.v31071, whitelistEncoding.v31072, whitelistEncoding.v31073, whitelistEncoding.v31074, whitelistEncoding.v31075, whitelistEncoding.v31076, whitelistEncoding.v31077, whitelistEncoding.v31078, whitelistEncoding.v31079, whitelistEncoding.v31080, whitelistEncoding.v31081, whitelistEncoding.v31082, whitelistEncoding.v31083, whitelistEncoding.v31084, whitelistEncoding.v31085, whitelistEncoding.v31086, whitelistEncoding.v31087, whitelistEncoding.v31088, whitelistEncoding.v31089, whitelistEncoding.v31090, bit_or_one_iff]
  simp

theorem execute_instruction_whitelist_cases (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (valid : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    WhitelistCases (EXUPair (run initial inputs (t + 1))).1 := by
  exact (allowed_instruction_cases _).mp
    (original_assumptions_execute_allowed initial inputs reset environment t valid)

theorem committed_instruction_whitelist_cases (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1) :
    WhitelistCases (WBUPair (run initial inputs (t + 2))).1 := by
  exact (allowed_instruction_cases _).mp
    (original_assumptions_committed_allowed initial inputs reset environment t commit)

#print axioms allowed_instruction_cases
#print axioms committed_instruction_whitelist_cases
end NutShellProofs
