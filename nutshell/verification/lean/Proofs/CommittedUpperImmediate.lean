import Proofs.ReferenceUpperSemantics
import Proofs.ReferenceAddi
namespace NutShellProofs
open nNutCore

theorem upper_match_low32 (operation : UpperImmediateOp) (instr : BitVec 64)
    (matched : IsUpperImmediate operation instr) :
    BitVec.extractLsb' 0 32 instr &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32 := by
  have low := congrArg (BitVec.extractLsb' 0 32) matched
  cases operation <;> simpa only [BitVec.extractLsb'_and] using low

private theorem upper_extract_low32 (instr : BitVec 64) :
    BitVec.extractLsb' 12 20 (BitVec.extractLsb' 0 32 instr) = BitVec.extractLsb' 12 20 instr := by
  apply BitVec.eq_of_getLsbD_eq
  intro k
  simp only [BitVec.getLsbD_extractLsb']
  by_cases small : k < 20
  · have bound : 12 + k < 32 := by omega
    simp [small, bound]
  · simp [small]

theorem committed_reference_upper_immediate (s : State) (i next : Inputs)
    (operation : UpperImmediateOp) (commit : v9 (step s i) next = 1)
    (matched : IsUpperImmediate operation s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    v16164 (step s i) next = immediateU s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr := by
  have low : v14575 (step s i) next &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32 := by
    rw [committed_reference_instruction s i next commit]
    exact upper_match_low32 operation _ matched
  have result : v16164 (step s i) next =
      (BitVec.extractLsb' 12 20 (v14575 (step s i) next) ++ (0 : BitVec 12)).signExtend 64 := by
    cases operation with
    | lui => exact reference_upper_lui_immediate _ _ commit low
    | auipc => exact reference_upper_auipc_immediate _ _ commit low
  rw [committed_reference_instruction s i next commit, upper_extract_low32] at result
  exact result

theorem writeback_lui_matches_reference_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsUpperImmediate .lui (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    v11842 (run initial inputs (t + 2)) (inputs (t + 2)) =
      v16164 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  exact (writeback_lui_run initial inputs reset t commit unit matched).trans
    (committed_reference_upper_immediate _ _ _ .lui commit matched).symm

#print axioms committed_reference_upper_immediate
#print axioms writeback_lui_matches_reference_run
end NutShellProofs
