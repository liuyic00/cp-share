import Proofs.ReferenceJumpDecode
import Proofs.JumpWriteback
import Proofs.DecodeCases
import Proofs.DestinationAlignment
namespace RiscvMiniProofs
open nCoreSoc

-- PC and target alignment remain explicit proof obligations, not assumptions
-- inserted into the generated environment.
theorem register_tasks_jal_commit (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (control : ControlAligned s)
    (reset : i.nreset = 0) (commit : v964 s i = 1) (env : assumes s i)
    (pc : WritebackPcAgreement s) (aligned : v2249 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) :
    RegisterTasks s i := by
  by_cases rd_zero : v701 s i = 0
  · exact register_tasks_rd_zero s i agree reset commit rd_zero
  · apply register_tasks_of_written_value s i agree reset commit
    have ctrl := control_values_at_commit s i control reset commit
    have sel := ctrl.write_select.trans (jal_write_select _ known)
    have enabled := ctrl.write_enable.trans (jal_write_enable _ known)
    rw [dut_jump_written_value s i reset (environment_no_trap s i reset env) sel enabled rd_zero,
      reference_jal_written_value s i reset commit aligned known rd_zero, reference_jal_link]
    exact congrArg (fun x : BitVec 32 => x + 4) pc

theorem register_tasks_jalr_commit (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (control : ControlAligned s)
    (reset : i.nreset = 0) (commit : v964 s i = 1) (env : assumes s i)
    (pc : WritebackPcAgreement s) (aligned : v2219 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) :
    RegisterTasks s i := by
  by_cases rd_zero : v701 s i = 0
  · exact register_tasks_rd_zero s i agree reset commit rd_zero
  · apply register_tasks_of_written_value s i agree reset commit
    have ctrl := control_values_at_commit s i control reset commit
    have sel := ctrl.write_select.trans (jalr_write_select _ known)
    have enabled := ctrl.write_enable.trans (jalr_write_enable _ known)
    rw [dut_jump_written_value s i reset (environment_no_trap s i reset env) sel enabled rd_zero,
      reference_jalr_written_value s i reset commit aligned known rd_zero, reference_jalr_link]
    exact congrArg (fun x : BitVec 32 => x + 4) pc

theorem jal_tasks_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (pc : WritebackPcAgreement (run initial inputs t))
    (aligned : BitVec.extractLsb' 0 2 (v2222 (run initial inputs t) (inputs t) + v2092 (run initial inputs t) (inputs t)) = 0)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) :
    RegisterTasks (run initial inputs t) (inputs t) := by
  have config := reference_config_reachable initial inputs cycles reset t ht
  exact register_tasks_jal_commit _ _ agree
    (control_alignment_reachable initial inputs cycles reset env t ht)
    (reset.2.2 t ht) commit (env t) pc
    ((reference_jal_alignment _ _ config).mpr aligned) known

#print axioms jal_tasks_reachable
theorem jalr_tasks_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (pc : WritebackPcAgreement (run initial inputs t))
    (aligned : BitVec.extractLsb' 0 2 (v2205 (run initial inputs t) (inputs t)) = 0)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) :
    RegisterTasks (run initial inputs t) (inputs t) := by
  have config := reference_config_reachable initial inputs cycles reset t ht
  exact register_tasks_jalr_commit _ _ agree
    (control_alignment_reachable initial inputs cycles reset env t ht)
    (reset.2.2 t ht) commit (env t) pc
    ((reference_jalr_alignment _ _ config).mpr aligned) known

#print axioms jalr_tasks_reachable
#print axioms register_tasks_jal_commit
#print axioms register_tasks_jalr_commit
end RiscvMiniProofs
