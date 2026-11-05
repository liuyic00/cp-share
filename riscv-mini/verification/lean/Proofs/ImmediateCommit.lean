import Proofs.ReferenceImmediateDecode
import Proofs.RegisterArithmeticCommit
import Proofs.DecodeCases
import Proofs.DestinationAlignment
namespace RiscvMiniProofs
open nCoreSoc

theorem register_tasks_addi_commit (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (control : ControlAligned s)
    (alu : DecodedAluAligned s) (zero : ReferenceZero s)
    (reset : i.nreset = 0) (commit : v964 s i = 1) (env : assumes s i)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : RegisterTasks s i := by
  by_cases rd_zero : v701 s i = 0
  · exact register_tasks_rd_zero s i agree reset commit rd_zero
  · apply register_tasks_of_written_value s i agree reset commit
    have ctrl := control_values_at_commit s i control reset commit
    have sel := ctrl.write_select.trans (addi_write_select _ known)
    have enabled := ctrl.write_enable.trans (addi_write_enable _ known)
    rw [dut_alu_written_value s i reset (environment_no_trap s i reset env) sel enabled rd_zero,
      reference_addi_written_value s i reset commit known rd_zero]
    exact aligned_reference_arithmetic_addi s i alu agree zero commit known
#print axioms register_tasks_addi_commit
theorem register_tasks_slti_commit (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (control : ControlAligned s)
    (alu : DecodedAluAligned s) (zero : ReferenceZero s)
    (reset : i.nreset = 0) (commit : v964 s i = 1) (env : assumes s i)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : RegisterTasks s i := by
  by_cases rd_zero : v701 s i = 0
  · exact register_tasks_rd_zero s i agree reset commit rd_zero
  · apply register_tasks_of_written_value s i agree reset commit
    have ctrl := control_values_at_commit s i control reset commit
    have sel := ctrl.write_select.trans (slti_write_select _ known)
    have enabled := ctrl.write_enable.trans (slti_write_enable _ known)
    rw [dut_alu_written_value s i reset (environment_no_trap s i reset env) sel enabled rd_zero,
      reference_slti_written_value s i reset commit known rd_zero]
    exact aligned_reference_arithmetic_slti s i alu agree zero commit known
#print axioms register_tasks_slti_commit
theorem register_tasks_sltiu_commit (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (control : ControlAligned s)
    (alu : DecodedAluAligned s) (zero : ReferenceZero s)
    (reset : i.nreset = 0) (commit : v964 s i = 1) (env : assumes s i)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : RegisterTasks s i := by
  by_cases rd_zero : v701 s i = 0
  · exact register_tasks_rd_zero s i agree reset commit rd_zero
  · apply register_tasks_of_written_value s i agree reset commit
    have ctrl := control_values_at_commit s i control reset commit
    have sel := ctrl.write_select.trans (sltiu_write_select _ known)
    have enabled := ctrl.write_enable.trans (sltiu_write_enable _ known)
    rw [dut_alu_written_value s i reset (environment_no_trap s i reset env) sel enabled rd_zero,
      reference_sltiu_written_value s i reset commit known rd_zero]
    exact aligned_reference_arithmetic_sltiu s i alu agree zero commit known
#print axioms register_tasks_sltiu_commit
theorem register_tasks_xori_commit (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (control : ControlAligned s)
    (alu : DecodedAluAligned s) (zero : ReferenceZero s)
    (reset : i.nreset = 0) (commit : v964 s i = 1) (env : assumes s i)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : RegisterTasks s i := by
  by_cases rd_zero : v701 s i = 0
  · exact register_tasks_rd_zero s i agree reset commit rd_zero
  · apply register_tasks_of_written_value s i agree reset commit
    have ctrl := control_values_at_commit s i control reset commit
    have sel := ctrl.write_select.trans (xori_write_select _ known)
    have enabled := ctrl.write_enable.trans (xori_write_enable _ known)
    rw [dut_alu_written_value s i reset (environment_no_trap s i reset env) sel enabled rd_zero,
      reference_xori_written_value s i reset commit known rd_zero]
    exact aligned_reference_arithmetic_xori s i alu agree zero commit known
#print axioms register_tasks_xori_commit
theorem register_tasks_ori_commit (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (control : ControlAligned s)
    (alu : DecodedAluAligned s) (zero : ReferenceZero s)
    (reset : i.nreset = 0) (commit : v964 s i = 1) (env : assumes s i)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : RegisterTasks s i := by
  by_cases rd_zero : v701 s i = 0
  · exact register_tasks_rd_zero s i agree reset commit rd_zero
  · apply register_tasks_of_written_value s i agree reset commit
    have ctrl := control_values_at_commit s i control reset commit
    have sel := ctrl.write_select.trans (ori_write_select _ known)
    have enabled := ctrl.write_enable.trans (ori_write_enable _ known)
    rw [dut_alu_written_value s i reset (environment_no_trap s i reset env) sel enabled rd_zero,
      reference_ori_written_value s i reset commit known rd_zero]
    exact aligned_reference_arithmetic_ori s i alu agree zero commit known
#print axioms register_tasks_ori_commit
theorem register_tasks_andi_commit (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (control : ControlAligned s)
    (alu : DecodedAluAligned s) (zero : ReferenceZero s)
    (reset : i.nreset = 0) (commit : v964 s i = 1) (env : assumes s i)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : RegisterTasks s i := by
  by_cases rd_zero : v701 s i = 0
  · exact register_tasks_rd_zero s i agree reset commit rd_zero
  · apply register_tasks_of_written_value s i agree reset commit
    have ctrl := control_values_at_commit s i control reset commit
    have sel := ctrl.write_select.trans (andi_write_select _ known)
    have enabled := ctrl.write_enable.trans (andi_write_enable _ known)
    rw [dut_alu_written_value s i reset (environment_no_trap s i reset env) sel enabled rd_zero,
      reference_andi_written_value s i reset commit known rd_zero]
    exact aligned_reference_arithmetic_andi s i alu agree zero commit known
#print axioms register_tasks_andi_commit
theorem register_tasks_slli_commit (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (control : ControlAligned s)
    (alu : DecodedAluAligned s) (zero : ReferenceZero s)
    (reset : i.nreset = 0) (commit : v964 s i = 1) (env : assumes s i)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : RegisterTasks s i := by
  by_cases rd_zero : v701 s i = 0
  · exact register_tasks_rd_zero s i agree reset commit rd_zero
  · apply register_tasks_of_written_value s i agree reset commit
    have ctrl := control_values_at_commit s i control reset commit
    have sel := ctrl.write_select.trans (slli_write_select _ known)
    have enabled := ctrl.write_enable.trans (slli_write_enable _ known)
    rw [dut_alu_written_value s i reset (environment_no_trap s i reset env) sel enabled rd_zero,
      reference_slli_written_value s i reset commit known rd_zero]
    exact aligned_reference_arithmetic_slli s i alu agree zero commit known
#print axioms register_tasks_slli_commit
theorem register_tasks_srli_commit (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (control : ControlAligned s)
    (alu : DecodedAluAligned s) (zero : ReferenceZero s)
    (reset : i.nreset = 0) (commit : v964 s i = 1) (env : assumes s i)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : RegisterTasks s i := by
  by_cases rd_zero : v701 s i = 0
  · exact register_tasks_rd_zero s i agree reset commit rd_zero
  · apply register_tasks_of_written_value s i agree reset commit
    have ctrl := control_values_at_commit s i control reset commit
    have sel := ctrl.write_select.trans (srli_write_select _ known)
    have enabled := ctrl.write_enable.trans (srli_write_enable _ known)
    rw [dut_alu_written_value s i reset (environment_no_trap s i reset env) sel enabled rd_zero,
      reference_srli_written_value s i reset commit known rd_zero]
    exact aligned_reference_arithmetic_srli s i alu agree zero commit known
#print axioms register_tasks_srli_commit
theorem register_tasks_srai_commit (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (control : ControlAligned s)
    (alu : DecodedAluAligned s) (zero : ReferenceZero s)
    (reset : i.nreset = 0) (commit : v964 s i = 1) (env : assumes s i)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : RegisterTasks s i := by
  by_cases rd_zero : v701 s i = 0
  · exact register_tasks_rd_zero s i agree reset commit rd_zero
  · apply register_tasks_of_written_value s i agree reset commit
    have ctrl := control_values_at_commit s i control reset commit
    have sel := ctrl.write_select.trans (srai_write_select _ known)
    have enabled := ctrl.write_enable.trans (srai_write_enable _ known)
    rw [dut_alu_written_value s i reset (environment_no_trap s i reset env) sel enabled rd_zero,
      reference_srai_written_value s i reset commit known rd_zero]
    exact aligned_reference_arithmetic_srai s i alu agree zero commit known
#print axioms register_tasks_srai_commit
def ImmediateInstruction (instruction : BitVec 32) : Prop :=
  instruction &&& 28799 = 19 ∨
  instruction &&& 28799 = 8211 ∨
  instruction &&& 28799 = 12307 ∨
  instruction &&& 28799 = 16403 ∨
  instruction &&& 28799 = 24595 ∨
  instruction &&& 28799 = 28691 ∨
  instruction &&& 4261441663 = 4115 ∨
  instruction &&& 4261441663 = 20499 ∨
  instruction &&& 4261441663 = 1073762323
theorem immediate_tasks_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (instruction : ImmediateInstruction
      (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) :
    RegisterTasks (run initial inputs t) (inputs t) := by
  have control := control_alignment_reachable initial inputs cycles reset env t ht
  have alu := decoded_alu_alignment_reachable initial inputs cycles reset env t ht
  have zero := reference_zero_reachable initial inputs cycles reset t ht
  rcases instruction with known | known | known | known | known | known | known | known | known
  · exact register_tasks_addi_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
  · exact register_tasks_slti_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
  · exact register_tasks_sltiu_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
  · exact register_tasks_xori_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
  · exact register_tasks_ori_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
  · exact register_tasks_andi_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
  · exact register_tasks_slli_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
  · exact register_tasks_srli_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
  · exact register_tasks_srai_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
#print axioms immediate_tasks_reachable
end RiscvMiniProofs
