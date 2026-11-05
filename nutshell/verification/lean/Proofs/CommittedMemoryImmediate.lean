import Proofs.ReferenceMemoryImmediate
import Proofs.StoreRegisterStep
namespace NutShellProofs
open nNutCore
private theorem memory_extract_low32 (instr : BitVec 64) (start len : Nat)
    (bound : start + len ≤ 32) :
    BitVec.extractLsb' start len (BitVec.extractLsb' 0 32 instr) = BitVec.extractLsb' start len instr := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit
  simp only [BitVec.getLsbD_extractLsb']
  by_cases small : bit < len
  · have inRange : start + bit < 32 := by omega
    simp [small, inRange]
  · simp [small]

theorem committed_reference_memory_immediate (s : State) (i next : Inputs)
    (operation : MemoryOp) (commit : v9 (step s i) next = 1)
    (matched : IsMemory operation (EXUPair s).1) :
    v16164 (step s i) next = memoryImmediate operation (EXUPair s).1 := by
  have low : v14575 (step s i) next &&& (28799 : BitVec 32) = operation.encoding.setWidth 32 := by
    rw [committed_reference_instruction s i next commit]
    exact store_match_low32 operation _ matched
  cases operation with
  | lb =>
    have result := reference_memory_imm_lb_immediate (step s i) next commit low
    rw [committed_reference_instruction s i next commit] at result
    simpa only [memoryImmediate, MemoryOp.isLoad, immediateI, immediateS, ↓reduceIte,
      memory_extract_low32 _ _ _ (by decide : 20 + 12 ≤ 32),
      memory_extract_low32 _ _ _ (by decide : 25 + 7 ≤ 32),
      memory_extract_low32 _ _ _ (by decide : 7 + 5 ≤ 32)] using result
  | lh =>
    have result := reference_memory_imm_lh_immediate (step s i) next commit low
    rw [committed_reference_instruction s i next commit] at result
    simpa only [memoryImmediate, MemoryOp.isLoad, immediateI, immediateS, ↓reduceIte,
      memory_extract_low32 _ _ _ (by decide : 20 + 12 ≤ 32),
      memory_extract_low32 _ _ _ (by decide : 25 + 7 ≤ 32),
      memory_extract_low32 _ _ _ (by decide : 7 + 5 ≤ 32)] using result
  | lw =>
    have result := reference_memory_imm_lw_immediate (step s i) next commit low
    rw [committed_reference_instruction s i next commit] at result
    simpa only [memoryImmediate, MemoryOp.isLoad, immediateI, immediateS, ↓reduceIte,
      memory_extract_low32 _ _ _ (by decide : 20 + 12 ≤ 32),
      memory_extract_low32 _ _ _ (by decide : 25 + 7 ≤ 32),
      memory_extract_low32 _ _ _ (by decide : 7 + 5 ≤ 32)] using result
  | ld =>
    have result := reference_memory_imm_ld_immediate (step s i) next commit low
    rw [committed_reference_instruction s i next commit] at result
    simpa only [memoryImmediate, MemoryOp.isLoad, immediateI, immediateS, ↓reduceIte,
      memory_extract_low32 _ _ _ (by decide : 20 + 12 ≤ 32),
      memory_extract_low32 _ _ _ (by decide : 25 + 7 ≤ 32),
      memory_extract_low32 _ _ _ (by decide : 7 + 5 ≤ 32)] using result
  | lbu =>
    have result := reference_memory_imm_lbu_immediate (step s i) next commit low
    rw [committed_reference_instruction s i next commit] at result
    simpa only [memoryImmediate, MemoryOp.isLoad, immediateI, immediateS, ↓reduceIte,
      memory_extract_low32 _ _ _ (by decide : 20 + 12 ≤ 32),
      memory_extract_low32 _ _ _ (by decide : 25 + 7 ≤ 32),
      memory_extract_low32 _ _ _ (by decide : 7 + 5 ≤ 32)] using result
  | lhu =>
    have result := reference_memory_imm_lhu_immediate (step s i) next commit low
    rw [committed_reference_instruction s i next commit] at result
    simpa only [memoryImmediate, MemoryOp.isLoad, immediateI, immediateS, ↓reduceIte,
      memory_extract_low32 _ _ _ (by decide : 20 + 12 ≤ 32),
      memory_extract_low32 _ _ _ (by decide : 25 + 7 ≤ 32),
      memory_extract_low32 _ _ _ (by decide : 7 + 5 ≤ 32)] using result
  | lwu =>
    have result := reference_memory_imm_lwu_immediate (step s i) next commit low
    rw [committed_reference_instruction s i next commit] at result
    simpa only [memoryImmediate, MemoryOp.isLoad, immediateI, immediateS, ↓reduceIte,
      memory_extract_low32 _ _ _ (by decide : 20 + 12 ≤ 32),
      memory_extract_low32 _ _ _ (by decide : 25 + 7 ≤ 32),
      memory_extract_low32 _ _ _ (by decide : 7 + 5 ≤ 32)] using result
  | sb =>
    have result := reference_memory_imm_sb_immediate (step s i) next commit low
    rw [committed_reference_instruction s i next commit] at result
    simpa only [memoryImmediate, MemoryOp.isLoad, immediateI, immediateS, ↓reduceIte,
      memory_extract_low32 _ _ _ (by decide : 20 + 12 ≤ 32),
      memory_extract_low32 _ _ _ (by decide : 25 + 7 ≤ 32),
      memory_extract_low32 _ _ _ (by decide : 7 + 5 ≤ 32)] using result
  | sh =>
    have result := reference_memory_imm_sh_immediate (step s i) next commit low
    rw [committed_reference_instruction s i next commit] at result
    simpa only [memoryImmediate, MemoryOp.isLoad, immediateI, immediateS, ↓reduceIte,
      memory_extract_low32 _ _ _ (by decide : 20 + 12 ≤ 32),
      memory_extract_low32 _ _ _ (by decide : 25 + 7 ≤ 32),
      memory_extract_low32 _ _ _ (by decide : 7 + 5 ≤ 32)] using result
  | sw =>
    have result := reference_memory_imm_sw_immediate (step s i) next commit low
    rw [committed_reference_instruction s i next commit] at result
    simpa only [memoryImmediate, MemoryOp.isLoad, immediateI, immediateS, ↓reduceIte,
      memory_extract_low32 _ _ _ (by decide : 20 + 12 ≤ 32),
      memory_extract_low32 _ _ _ (by decide : 25 + 7 ≤ 32),
      memory_extract_low32 _ _ _ (by decide : 7 + 5 ≤ 32)] using result
  | sd =>
    have result := reference_memory_imm_sd_immediate (step s i) next commit low
    rw [committed_reference_instruction s i next commit] at result
    simpa only [memoryImmediate, MemoryOp.isLoad, immediateI, immediateS, ↓reduceIte,
      memory_extract_low32 _ _ _ (by decide : 20 + 12 ≤ 32),
      memory_extract_low32 _ _ _ (by decide : 25 + 7 ≤ 32),
      memory_extract_low32 _ _ _ (by decide : 7 + 5 ≤ 32)] using result
#print axioms committed_reference_memory_immediate
theorem memory_immediate_matches_reference_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : MemoryOp)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1) :
    v11595 (run initial inputs (t + 1)) (inputs (t + 1)) =
      v16164 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  have decoded := (memory_decode_run initial inputs reset t).2
    (commit_requires_execute_valid _ _ _ commit) operation matched unit
  exact decoded.2.2.2.1.trans
    (committed_reference_memory_immediate _ _ _ operation commit matched).symm
#print axioms memory_immediate_matches_reference_run
end NutShellProofs
