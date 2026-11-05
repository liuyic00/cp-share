import Proofs.ReferenceJump
import Proofs.PcRelation
namespace RiscvMiniProofs
open nCoreSoc

theorem jump_writeback_value (s : State) (i : Inputs)
    (sel : s.g4.r131_ndut_5Fdpath_5Fwb_5Fsel = 2) :
    v765 s i = s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc + 4 := by
  have extract : BitVec.extractLsb' 0 32 ((0#1) ++ v713 s i) = v713 s i := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp [BitVec.getLsbD_append (n := 1) (m := 32), hj]
  have selected : v765 s i = v713 s i := by
    simpa [v765, v764, v763, v762, v714, v707, v709, v155, v38, v4, sel] using extract
  rw [selected]
  change BitVec.extractLsb' 0 32 (((0#1) ++ s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc) + (4#33)) = _
  rw [show (4#33) = (0#1) ++ (4#32) by decide]
  exact reference_execution_add _ _

theorem dut_jump_written_value (s : State) (i : Inputs)
    (reset : i.nreset = 0) (trap : v182 s i = 0)
    (sel : s.g4.r131_ndut_5Fdpath_5Fwb_5Fsel = 2)
    (enabled : s.g4.r132_ndut_5Fdpath_5Fwb_5Fen = 1) (nonzero : v701 s i ≠ 0) :
    dutRead (step s i) (v701 s i) = s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc + 4 := by
  rw [dut_read_after_step s i reset, jump_writeback_value s i sel]
  have stall := no_stall_after_reset s i reset
  have nz : v701 s i ≠ 0#5 := nonzero
  simp [nz, v704, v703, v702, v700, v699, v698, v697, v696,
    v150, v4, stall, trap, enabled]

theorem jump_writeback_matches_reference (s : State) (i : Inputs)
    (sel : s.g4.r131_ndut_5Fdpath_5Fwb_5Fsel = 2) (pc : WritebackPcAgreement s) :
    v765 s i = v2255 s i ∧ v765 s i = v2226 s i := by
  have eq : s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc = v2222 s i := pc
  rw [jump_writeback_value s i sel, reference_jal_link, reference_jalr_link, eq]
  exact ⟨rfl, rfl⟩

#print axioms jump_writeback_value
#print axioms dut_jump_written_value
#print axioms jump_writeback_matches_reference
end RiscvMiniProofs
