import Proofs.AluSemantics

namespace RiscvMiniProofs
open nCoreSoc

-- Exact stage transfer, before proving the forwarded operands equal the
-- architectural operands. The latter is a separate outstanding obligation.
structure ExecuteTransfer (before after : State) (i : Inputs) : Prop where
  instruction : after.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst =
    before.g3.r123_ndut_5Fdpath_5Ffe_5Freg_5Finst
  pc : after.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
    before.g3.r124_ndut_5Fdpath_5Ffe_5Freg_5Fpc
  alu : after.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu =
    circuitAlu (v7840 before i) (v7889 before i) (v8034 before i)
  csr_input : after.g4.r128_ndut_5Fdpath_5Few_5Freg_5F_5Fcsr_5Fin = v8169 before i

theorem execute_transfer_step (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) : ExecuteTransfer s (step s i) i := by
  have stall := no_stall_after_reset s i reset
  have trap := environment_no_trap s i reset env
  have advance : v7777 s i = 1 := by
    simp [v7777, v7775, v7776, stall, trap, v4]
  have keep : v7774 s i = 0 := by
    simp [v7774, v7773, v7772, stall, trap, v1, v0, reset, v4]
  constructor
  · change v7780 s i = _
    simp [v7780, v7779, v7778, keep, advance, v1, v0, reset]
  · change v7783 s i = _
    simp [v7783, v7782, v7781, keep, advance, v1, v0, reset]
  · change v8167 s i = _
    simp [v8167, v8166, v8165, keep, advance, v1, v0, reset, circuit_alu_eq]
  · change v8172 s i = _
    simp [v8172, v8171, v8170, keep, advance, v1, v0, reset]

theorem execute_transfer_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles)
    (env : Environment initial inputs) (t : Nat) (ht : cycles ≤ t) :
    ExecuteTransfer (run initial inputs t) (run initial inputs (t+1)) (inputs t) := by
  exact execute_transfer_step _ _ (reset.2.2 t ht) (env t)

-- The actual generated writeback ALU register implements aluSpec on the
-- actual execution-stage operands. Architectural operand alignment is separate.
theorem execute_alu_correct_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles)
    (env : Environment initial inputs) (t : Nat) (ht : cycles ≤ t) :
    (run initial inputs (t+1)).g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu =
      aluSpec (v7840 (run initial inputs t) (inputs t))
        (v7889 (run initial inputs t) (inputs t))
        (v8034 (run initial inputs t) (inputs t)) := by
  exact (execute_transfer_reachable initial inputs cycles reset env t ht).alu.trans
    (circuit_alu_correct _ _ _)

#print axioms execute_alu_correct_reachable
#print axioms execute_transfer_reachable
end RiscvMiniProofs
