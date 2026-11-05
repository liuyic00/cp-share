import Proofs.LoadWordValue
import Proofs.ReferenceLoadWriteback
namespace RiscvMiniProofs
open nCoreSoc

theorem dut_load_written_value (s : State) (i : Inputs)
    (reset : i.nreset = 0) (trap : v182 s i = 0)
    (enabled : s.g4.r132_ndut_5Fdpath_5Fwb_5Fen = 1) (nonzero : v701 s i ≠ 0) :
    dutRead (step s i) (v701 s i) = v765 s i := by
  rw [dut_read_after_step s i reset]
  have stall := no_stall_after_reset s i reset
  have nz : v701 s i ≠ 0#5 := nonzero
  simp [nz, v704, v703, v702, v700, v699, v698, v697, v696,
    v150, v4, stall, trap, enabled]

theorem lw_tasks_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) :
    RegisterTasks (run initial inputs t) (inputs t) := by
  by_cases rd_zero : v701 (run initial inputs t) (inputs t) = 0
  · exact register_tasks_rd_zero _ _ agree (reset.2.2 t ht) commit rd_zero
  · have control := control_values_at_commit _ _
      (control_alignment_reachable initial inputs cycles reset env t ht) (reset.2.2 t ht) commit
    have enabled := control.write_enable.trans (lw_write_enable _ known)
    have kind := control.load.trans (lw_load _ known)
    have trap := environment_no_trap _ _ (reset.2.2 t ht) (env t)
    have address := load_address_reachable initial inputs cycles reset env t ht agree commit
      (LoadInstruction.op_lw known)
    have aligned := no_trap_word_load _ _ trap kind
    rw [address] at aligned
    have refAligned : v2139 (run initial inputs t) (inputs t) = 1#1 := by
      change (if BitVec.extractLsb' 0 2 (v2095 (run initial inputs t) (inputs t)) = 0#2 then 1 else 0) = 1#1
      exact if_pos aligned
    apply register_tasks_of_written_value _ _ agree (reset.2.2 t ht) commit
    rw [dut_load_written_value _ _ (reset.2.2 t ht) trap enabled rd_zero,
      reference_lw_written_value _ _ (reset.2.2 t ht) commit refAligned known rd_zero]
    exact load_word_value_reachable initial inputs cycles reset env t ht agree commit known

inductive SubwordLoadInstruction (instruction : BitVec 32) : Prop where
  | lb : instruction &&& 28799 = 3 → SubwordLoadInstruction instruction
  | lh : instruction &&& 28799 = 4099 → SubwordLoadInstruction instruction
  | lbu : instruction &&& 28799 = 16387 → SubwordLoadInstruction instruction
  | lhu : instruction &&& 28799 = 20483 → SubwordLoadInstruction instruction

-- This reduction still requires the global PC and subword-load obligations.
theorem register_tasks_reachable_of_pc_and_subword (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (pc : WritebackPcAgreement (run initial inputs t))
    (loads : SubwordLoadInstruction (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst →
      dutRead (step (run initial inputs t) (inputs t)) (v701 (run initial inputs t) (inputs t)) =
        referenceRead (step (run initial inputs t) (inputs t)) (v701 (run initial inputs t) (inputs t))) :
    RegisterTasks (run initial inputs t) (inputs t) := by
  apply register_tasks_reachable_of_pc_and_loads initial inputs cycles reset env t ht agree commit pc
  intro instruction
  cases instruction with
  | op_lb known => exact loads (SubwordLoadInstruction.lb known)
  | op_lh known => exact loads (SubwordLoadInstruction.lh known)
  | op_lbu known => exact loads (SubwordLoadInstruction.lbu known)
  | op_lhu known => exact loads (SubwordLoadInstruction.lhu known)
  | op_lw known =>
    exact (register_tasks_iff_written_value _ _ agree (reset.2.2 t ht) commit).mp
      (lw_tasks_reachable initial inputs cycles reset env t ht agree commit known)

#print axioms register_tasks_reachable_of_pc_and_subword
#print axioms dut_load_written_value
#print axioms lw_tasks_reachable
end RiscvMiniProofs
