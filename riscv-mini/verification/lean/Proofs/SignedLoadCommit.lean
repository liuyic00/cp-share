import Proofs.LoadWordCommit
import Proofs.SignedLoadValue
import Proofs.UnsignedLoadCommit
namespace RiscvMiniProofs
open nCoreSoc

theorem lb_tasks_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) :
    RegisterTasks (run initial inputs t) (inputs t) := by
  by_cases rd_zero : v701 (run initial inputs t) (inputs t) = 0
  · exact register_tasks_rd_zero _ _ agree (reset.2.2 t ht) commit rd_zero
  · have control := control_values_at_commit _ _
      (control_alignment_reachable initial inputs cycles reset env t ht) (reset.2.2 t ht) commit
    have enabled := control.write_enable.trans (lb_write_enable _ known)
    have trap := environment_no_trap _ _ (reset.2.2 t ht) (env t)
    apply register_tasks_of_written_value _ _ agree (reset.2.2 t ht) commit
    rw [dut_load_written_value _ _ (reset.2.2 t ht) trap enabled rd_zero,
      reference_lb_written_value _ _ (reset.2.2 t ht) commit known rd_zero]
    exact lb_value_reachable initial inputs cycles reset env t ht agree commit known

theorem lh_tasks_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) :
    RegisterTasks (run initial inputs t) (inputs t) := by
  by_cases rd_zero : v701 (run initial inputs t) (inputs t) = 0
  · exact register_tasks_rd_zero _ _ agree (reset.2.2 t ht) commit rd_zero
  · have control := control_values_at_commit _ _
      (control_alignment_reachable initial inputs cycles reset env t ht) (reset.2.2 t ht) commit
    have enabled := control.write_enable.trans (lh_write_enable _ known)
    have kind := control.load.trans (lh_load _ known)
    have trap := environment_no_trap _ _ (reset.2.2 t ht) (env t)
    have address := load_address_reachable initial inputs cycles reset env t ht agree commit
      (LoadInstruction.op_lh known)
    have aligned := no_trap_signed_half_load _ _ trap kind
    rw [address] at aligned
    have refAligned : v2159 (run initial inputs t) (inputs t) = 1#1 := by
      change (if BitVec.extractLsb' 0 1 (v2095 (run initial inputs t) (inputs t)) = 0#1 then 1 else 0) = 1#1
      exact if_pos aligned
    apply register_tasks_of_written_value _ _ agree (reset.2.2 t ht) commit
    rw [dut_load_written_value _ _ (reset.2.2 t ht) trap enabled rd_zero,
      reference_lh_written_value _ _ (reset.2.2 t ht) commit refAligned known rd_zero]
    exact lh_value_reachable initial inputs cycles reset env t ht agree commit known

theorem register_tasks_reachable_of_pc (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (pc : WritebackPcAgreement (run initial inputs t)) :
    RegisterTasks (run initial inputs t) (inputs t) := by
  apply register_tasks_reachable_of_pc_and_signed_loads initial inputs cycles reset env t ht agree commit pc
  intro instruction
  cases instruction with
  | lb known =>
    exact (register_tasks_iff_written_value _ _ agree (reset.2.2 t ht) commit).mp
      (lb_tasks_reachable initial inputs cycles reset env t ht agree commit known)
  | lh known =>
    exact (register_tasks_iff_written_value _ _ agree (reset.2.2 t ht) commit).mp
      (lh_tasks_reachable initial inputs cycles reset env t ht agree commit known)

#print axioms lb_tasks_reachable
#print axioms lh_tasks_reachable
#print axioms register_tasks_reachable_of_pc
end RiscvMiniProofs
