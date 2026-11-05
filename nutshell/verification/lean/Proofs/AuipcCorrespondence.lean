import Proofs.UpperRegisterStep
import Proofs.EventPC
namespace NutShellProofs
open nNutCore

/-- Explicit dependency on the original PC assertion; it is not discharged here. -/
theorem committed_operand_pc_from_task10 (s : State) (i next : Inputs)
    (reset : next.g0.nreset = 0) (commit : v9 (step s i) next = 1)
    (pc : TaskHolds 10 (step s i) next) :
    extendOperandPC s.g47.r1513_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Fpc = v16457 (step s i) next := by
  have check : v31361 (step s i) next ≠ 1 ∨ v31359 (step s i) next = 1 := of_decide_eq_true pc
  have gate : v31361 (step s i) next = 1 := by
    simp [v31361, v14558, commit, v31360, v14554, v14553, v11455, v24, reset]
  have compare := check.resolve_left (not_not_intro gate)
  have same : v31357 (step s i) next = v31358 (step s i) next := by
    simpa [v31359] using compare
  have capture := capture_decode_cf_pc s i next commit
  have captured : v31357 (step s i) next =
      extendOperandPC s.g47.r1513_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Fpc :=
    congrArg extendOperandPC capture
  exact captured.symm.trans same

theorem reference_auipc_result (s : State) (i : Inputs) :
    v16543 s i = v16457 s i + v16164 s i := by
  simp only [v16543, v16542, v16540, v16541, low_add _ _ (by decide : 64 ≤ 65),
    BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 64 ≤ 64), BitVec.extractLsb'_eq_self]

theorem writeback_auipc_matches_reference_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsUpperImmediate .auipc (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr)
    (pc : TaskHolds 10 (run initial inputs (t + 2)) (inputs (t + 2))) :
    v11842 (run initial inputs (t + 2)) (inputs (t + 2)) =
      referenceUpperResult .auipc (run initial inputs (t + 2)) (inputs (t + 2)) := by
  have pcs := committed_operand_pc_from_task10 _ _ _ currentReset commit pc
  have imm := committed_reference_upper_immediate _ _ _ .auipc commit matched
  have result := writeback_auipc_run initial inputs reset t commit unit matched
  change _ = v16543 _ _
  rw [reference_auipc_result]
  exact result.trans (congr (congrArg (fun x : BitVec 64 => fun y : BitVec 64 => x + y) pcs) imm.symm)

#print axioms committed_operand_pc_from_task10
#print axioms writeback_auipc_matches_reference_run
theorem auipc_registers_aligned_run_step (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (immediate : IsUpperImmediate UpperImmediateOp.auipc (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (pc : TaskHolds 10 (run initial inputs (t + 2)) (inputs (t + 2))) :
    ArchitecturalRegistersAligned (run initial inputs (t + 3)) := by
  have matched : v14575 (run initial inputs (t + 2)) (inputs (t + 2)) &&&
      UpperImmediateOp.auipc.mask.setWidth 32 = UpperImmediateOp.auipc.encoding.setWidth 32 := by
    have instr : v14575 (run initial inputs (t + 2)) (inputs (t + 2)) =
        BitVec.extractLsb' 0 32 (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr :=
      committed_reference_instruction _ _ _ commit
    rw [instr]
    exact upper_match_low32 UpperImmediateOp.auipc _ immediate
  have write := writeback_upper_enabled_run initial inputs reset t UpperImmediateOp.auipc commit unit immediate
  have destination := committed_upper_destination_agrees _ _ _ UpperImmediateOp.auipc
    (destination1_decode_run initial inputs reset t).2 commit write immediate
  exact upper_registers_aligned_step _ _ UpperImmediateOp.auipc currentReset commit matched aligned destination write
    (writeback_auipc_matches_reference_run initial inputs reset t currentReset commit unit immediate pc)

#print axioms auipc_registers_aligned_run_step
end NutShellProofs
