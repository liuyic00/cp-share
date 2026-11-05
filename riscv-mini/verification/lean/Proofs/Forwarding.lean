import Proofs.RegisterReads
import Proofs.Pipeline
namespace RiscvMiniProofs
open nCoreSoc

theorem alu_writeback_value (s : State) (i : Inputs)
    (sel : s.g4.r131_ndut_5Fdpath_5Fwb_5Fsel = 0) :
    v765 s i = s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu := by
  simp [v765, v764, v763, v762, v761, v760, v707, v709, v715,
    v155, v38, v42, v4, sel]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp [BitVec.getLsbD_append (n := 1) (m := 32), hj]

-- With ALU writeback selected, bypass observes the next register-file value.
theorem alu_forwarding_port1 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (trap : v182 s i = 0)
    (sel : s.g4.r131_ndut_5Fdpath_5Fwb_5Fsel = 0) :
    v7629 s i = dutRead (step s i) (v7537 s i) := by
  rw [dut_read_after_step s i reset, alu_writeback_value s i sel]
  have stall := no_stall_after_reset s i reset
  have bound := s.g4.r132_ndut_5Fdpath_5Fwb_5Fen.isLt
  have cases : s.g4.r132_ndut_5Fdpath_5Fwb_5Fen = 0 ∨
      s.g4.r132_ndut_5Fdpath_5Fwb_5Fen = 1 := by
    have h : s.g4.r132_ndut_5Fdpath_5Fwb_5Fen.toNat = 0 ∨
        s.g4.r132_ndut_5Fdpath_5Fwb_5Fen.toNat = 1 := by omega
    rcases h with h | h
    · exact Or.inl (BitVec.eq_of_toNat_eq h)
    · exact Or.inr (BitVec.eq_of_toNat_eq h)
  rcases cases with en | en
  all_goals by_cases zero : v7537 s i = 0#5
  all_goals by_cases same : v701 s i = v7537 s i
  all_goals simp [v7629, dut_read_port1, v7536, v7538, v7539, v7540, v7541, v7542,
    v704, v703, v702, v700, v699, v698, v697, v696, v150, v32, v4,
    stall, trap, sel, en, zero, same, eq_comm, dutRead]

-- With ALU writeback selected, bypass observes the next register-file value.
theorem alu_forwarding_port2 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (trap : v182 s i = 0)
    (sel : s.g4.r131_ndut_5Fdpath_5Fwb_5Fsel = 0) :
    v7725 s i = dutRead (step s i) (v7633 s i) := by
  rw [dut_read_after_step s i reset, alu_writeback_value s i sel]
  have stall := no_stall_after_reset s i reset
  have bound := s.g4.r132_ndut_5Fdpath_5Fwb_5Fen.isLt
  have cases : s.g4.r132_ndut_5Fdpath_5Fwb_5Fen = 0 ∨
      s.g4.r132_ndut_5Fdpath_5Fwb_5Fen = 1 := by
    have h : s.g4.r132_ndut_5Fdpath_5Fwb_5Fen.toNat = 0 ∨
        s.g4.r132_ndut_5Fdpath_5Fwb_5Fen.toNat = 1 := by omega
    rcases h with h | h
    · exact Or.inl (BitVec.eq_of_toNat_eq h)
    · exact Or.inr (BitVec.eq_of_toNat_eq h)
  rcases cases with en | en
  all_goals by_cases zero : v7633 s i = 0#5
  all_goals by_cases same : v701 s i = v7633 s i
  all_goals simp [v7725, dut_read_port2, v7632, v7634, v7635, v7636, v7637, v7638,
    v704, v703, v702, v700, v699, v698, v697, v696, v150, v32, v4,
    stall, trap, sel, en, zero, same, eq_comm, dutRead]
#print axioms alu_forwarding_port1
#print axioms alu_forwarding_port2
end RiscvMiniProofs
