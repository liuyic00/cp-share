import Proofs.DestinationDecode
import Proofs.WritebackOrigin
import Proofs.ReferenceAddiRegisters
namespace NutShellProofs
open nNutCore

theorem committed_dut_destination (s : State) (i next : Inputs)
    (decoded : ExecuteDestination1Decoded s)
    (write : v11462 (step s i) next = 1) :
    v11465 (step s i) next = BitVec.extractLsb' 7 5
      s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr := by
  rcases next_writeback_origin s i next write with ⟨valid, enabled, dest⟩
  exact dest.trans (decoded valid enabled)

private theorem destination_low32 (instr : BitVec 64) :
    BitVec.extractLsb' 7 5 (BitVec.extractLsb' 0 32 instr) =
      BitVec.extractLsb' 7 5 instr := by
  apply BitVec.eq_of_getLsbD_eq
  intro k
  simp only [BitVec.getLsbD_extractLsb']
  by_cases small : k < 5
  · have bound : 7 + k < 32 := by omega
    simp [small, bound]
  · simp [small]

theorem committed_addi_destination_agrees (s : State) (i next : Inputs)
    (decoded : ExecuteDestination1Decoded s)
    (commit : v9 (step s i) next = 1)
    (write : v11462 (step s i) next = 1)
    (addi : IsADDI s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    v11465 (step s i) next = v15142 (step s i) next := by
  have matched : v14575 (step s i) next &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 19 := by
    rw [committed_reference_instruction s i next commit]
    exact addi_match_low32 _ addi
  rw [reference_addi_destination _ _ commit matched,
    committed_reference_instruction s i next commit, destination_low32]
  exact committed_dut_destination s i next decoded write

#print axioms committed_dut_destination
#print axioms committed_addi_destination_agrees
end NutShellProofs
