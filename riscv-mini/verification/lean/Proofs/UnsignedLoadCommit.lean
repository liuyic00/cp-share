import Proofs.LoadWordCommit
import Proofs.UnsignedLoadValue
namespace RiscvMiniProofs
open nCoreSoc

theorem lbu_tasks_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) :
    RegisterTasks (run initial inputs t) (inputs t) := by
  by_cases rd_zero : v701 (run initial inputs t) (inputs t) = 0
  · exact register_tasks_rd_zero _ _ agree (reset.2.2 t ht) commit rd_zero
  · have control := control_values_at_commit _ _
      (control_alignment_reachable initial inputs cycles reset env t ht) (reset.2.2 t ht) commit
    have enabled := control.write_enable.trans (lbu_write_enable _ known)
    have trap := environment_no_trap _ _ (reset.2.2 t ht) (env t)
    apply register_tasks_of_written_value _ _ agree (reset.2.2 t ht) commit
    rw [dut_load_written_value _ _ (reset.2.2 t ht) trap enabled rd_zero,
      reference_lbu_written_value _ _ (reset.2.2 t ht) commit known rd_zero]
    exact lbu_value_reachable initial inputs cycles reset env t ht agree commit known

theorem lhu_tasks_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) :
    RegisterTasks (run initial inputs t) (inputs t) := by
  by_cases rd_zero : v701 (run initial inputs t) (inputs t) = 0
  · exact register_tasks_rd_zero _ _ agree (reset.2.2 t ht) commit rd_zero
  · have control := control_values_at_commit _ _
      (control_alignment_reachable initial inputs cycles reset env t ht) (reset.2.2 t ht) commit
    have enabled := control.write_enable.trans (lhu_write_enable _ known)
    have kind := control.load.trans (lhu_load _ known)
    have trap := environment_no_trap _ _ (reset.2.2 t ht) (env t)
    have address := load_address_reachable initial inputs cycles reset env t ht agree commit
      (LoadInstruction.op_lhu known)
    have aligned := no_trap_unsigned_half_load _ _ trap kind
    rw [address] at aligned
    have refAligned : v2097 (run initial inputs t) (inputs t) = 1#1 := by
      change (if BitVec.extractLsb' 0 1 (v2095 (run initial inputs t) (inputs t)) = 0#1 then 1 else 0) = 1#1
      exact if_pos aligned
    apply register_tasks_of_written_value _ _ agree (reset.2.2 t ht) commit
    rw [dut_load_written_value _ _ (reset.2.2 t ht) trap enabled rd_zero,
      reference_lhu_written_value _ _ (reset.2.2 t ht) commit refAligned known rd_zero]
    exact lhu_value_reachable initial inputs cycles reset env t ht agree commit known

inductive SignedLoadInstruction (instruction : BitVec 32) : Prop where
  | lb : instruction &&& 28799 = 3 → SignedLoadInstruction instruction
  | lh : instruction &&& 28799 = 4099 → SignedLoadInstruction instruction

-- This reduction still requires the global PC and signed-load obligations.
theorem register_tasks_reachable_of_pc_and_signed_loads (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (pc : WritebackPcAgreement (run initial inputs t))
    (loads : SignedLoadInstruction (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst →
      dutRead (step (run initial inputs t) (inputs t)) (v701 (run initial inputs t) (inputs t)) =
        referenceRead (step (run initial inputs t) (inputs t)) (v701 (run initial inputs t) (inputs t))) :
    RegisterTasks (run initial inputs t) (inputs t) := by
  apply register_tasks_reachable_of_pc_and_loads initial inputs cycles reset env t ht agree commit pc
  intro instruction
  cases instruction with
  | op_lb known => exact loads (SignedLoadInstruction.lb known)
  | op_lh known => exact loads (SignedLoadInstruction.lh known)
  | op_lbu known =>
    exact (register_tasks_iff_written_value _ _ agree (reset.2.2 t ht) commit).mp
      (lbu_tasks_reachable initial inputs cycles reset env t ht agree commit known)
  | op_lhu known =>
    exact (register_tasks_iff_written_value _ _ agree (reset.2.2 t ht) commit).mp
      (lhu_tasks_reachable initial inputs cycles reset env t ht agree commit known)
  | op_lw known =>
    exact (register_tasks_iff_written_value _ _ agree (reset.2.2 t ht) commit).mp
      (lw_tasks_reachable initial inputs cycles reset env t ht agree commit known)

#print axioms register_tasks_reachable_of_pc_and_signed_loads
#print axioms lbu_tasks_reachable
#print axioms lhu_tasks_reachable
end RiscvMiniProofs
