import Proofs.ReferenceBranchImmediate
namespace NutShellProofs
open nNutCore

private theorem extract_low32 (x : BitVec 64) (start len : Nat) (bound : start + len ≤ 32) :
    BitVec.extractLsb' start len (BitVec.extractLsb' 0 32 x) = BitVec.extractLsb' start len x := by
  apply BitVec.eq_of_getLsbD_eq
  intro k
  simp only [BitVec.getLsbD_extractLsb']
  by_cases small : k < len
  · have b : start + k < 32 := by omega
    simp [small, b]
  · simp [small]

theorem committed_reference_branch_immediate (s : State) (i next : Inputs)
    (operation : BranchOp) (commit : v9 (step s i) next = 1)
    (matched : IsBranch operation s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    v16164 (step s i) next = immediateB s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr := by
  have low : v14575 (step s i) next &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32 := by
    rw [committed_reference_instruction s i next commit]
    exact branch_match_low32 operation _ matched
  cases operation with
  | beq =>
    have result := reference_branch_imm_beq_immediate _ _ commit low
    rw [committed_reference_instruction s i next commit] at result
    simpa (disch := omega) only [immediateB, extract_low32] using result
  | bne =>
    have result := reference_branch_imm_bne_immediate _ _ commit low
    rw [committed_reference_instruction s i next commit] at result
    simpa (disch := omega) only [immediateB, extract_low32] using result
  | blt =>
    have result := reference_branch_imm_blt_immediate _ _ commit low
    rw [committed_reference_instruction s i next commit] at result
    simpa (disch := omega) only [immediateB, extract_low32] using result
  | bge =>
    have result := reference_branch_imm_bge_immediate _ _ commit low
    rw [committed_reference_instruction s i next commit] at result
    simpa (disch := omega) only [immediateB, extract_low32] using result
  | bltu =>
    have result := reference_branch_imm_bltu_immediate _ _ commit low
    rw [committed_reference_instruction s i next commit] at result
    simpa (disch := omega) only [immediateB, extract_low32] using result
  | bgeu =>
    have result := reference_branch_imm_bgeu_immediate _ _ commit low
    rw [committed_reference_instruction s i next commit] at result
    simpa (disch := omega) only [immediateB, extract_low32] using result

#print axioms committed_reference_branch_immediate
end NutShellProofs
