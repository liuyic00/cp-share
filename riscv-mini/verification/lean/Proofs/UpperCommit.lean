import Proofs.ReferenceUpperDecode
import Proofs.RegisterArithmeticCommit
import Proofs.DecodeCases
import Proofs.DestinationAlignment
namespace RiscvMiniProofs
open nCoreSoc

theorem register_tasks_lui_commit (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (control : ControlAligned s)
    (alu : DecodedAluAligned s) (zero : ReferenceZero s)
    (reset : i.nreset = 0) (commit : v964 s i = 1) (env : assumes s i)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : RegisterTasks s i := by
  by_cases rd_zero : v701 s i = 0
  · exact register_tasks_rd_zero s i agree reset commit rd_zero
  · apply register_tasks_of_written_value s i agree reset commit
    have ctrl := control_values_at_commit s i control reset commit
    have sel := ctrl.write_select.trans (lui_write_select _ known)
    have enabled := ctrl.write_enable.trans (lui_write_enable _ known)
    rw [dut_alu_written_value s i reset (environment_no_trap s i reset env) sel enabled rd_zero,
      reference_lui_written_value s i reset commit known rd_zero]
    exact aligned_reference_arithmetic_lui s i alu agree zero commit known
#print axioms register_tasks_lui_commit
theorem register_tasks_auipc_commit (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (control : ControlAligned s)
    (alu : DecodedAluAligned s) (zero : ReferenceZero s)
    (reset : i.nreset = 0) (commit : v964 s i = 1) (env : assumes s i)
    (pc : WritebackPcAgreement s)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : RegisterTasks s i := by
  by_cases rd_zero : v701 s i = 0
  · exact register_tasks_rd_zero s i agree reset commit rd_zero
  · apply register_tasks_of_written_value s i agree reset commit
    have ctrl := control_values_at_commit s i control reset commit
    have sel := ctrl.write_select.trans (auipc_write_select _ known)
    have enabled := ctrl.write_enable.trans (auipc_write_enable _ known)
    rw [dut_alu_written_value s i reset (environment_no_trap s i reset env) sel enabled rd_zero,
      reference_auipc_written_value s i reset commit known rd_zero]
    exact aligned_reference_arithmetic_auipc s i alu agree zero commit pc known
#print axioms register_tasks_auipc_commit
def UpperInstruction (instruction : BitVec 32) : Prop :=
  instruction &&& 127 = 55 ∨
  instruction &&& 127 = 23
theorem upper_tasks_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (pc : WritebackPcAgreement (run initial inputs t))
    (instruction : UpperInstruction
      (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) :
    RegisterTasks (run initial inputs t) (inputs t) := by
  have control := control_alignment_reachable initial inputs cycles reset env t ht
  have alu := decoded_alu_alignment_reachable initial inputs cycles reset env t ht
  have zero := reference_zero_reachable initial inputs cycles reset t ht
  rcases instruction with known | known
  · exact register_tasks_lui_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
  · exact register_tasks_auipc_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) pc known
#print axioms upper_tasks_reachable
theorem lui_tasks_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (instruction : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) :
    RegisterTasks (run initial inputs t) (inputs t) :=
  register_tasks_lui_commit _ _ agree
    (control_alignment_reachable initial inputs cycles reset env t ht)
    (decoded_alu_alignment_reachable initial inputs cycles reset env t ht)
    (reference_zero_reachable initial inputs cycles reset t ht)
    (reset.2.2 t ht) commit (env t) instruction
#print axioms lui_tasks_reachable
end RiscvMiniProofs
