import Proofs.ReferenceRegisterDecode
import Proofs.DecodeCases
import Proofs.DestinationAlignment
namespace RiscvMiniProofs
open nCoreSoc
theorem dut_alu_written_value (s : State) (i : Inputs)
    (reset : i.nreset = 0) (trap : v182 s i = 0)
    (sel : s.g4.r131_ndut_5Fdpath_5Fwb_5Fsel = 0)
    (enabled : s.g4.r132_ndut_5Fdpath_5Fwb_5Fen = 1) (nonzero : v701 s i ≠ 0) :
    dutRead (step s i) (v701 s i) = s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu := by
  rw [dut_read_after_step s i reset, alu_writeback_value s i sel]
  have stall := no_stall_after_reset s i reset
  have nz : v701 s i ≠ 0#5 := nonzero
  simp [nz, v704, v703, v702, v700, v699, v698, v697, v696,
    v150, v4, stall, trap, enabled]

theorem register_tasks_add_commit (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (control : ControlAligned s)
    (alu : DecodedAluAligned s) (zero : ReferenceZero s)
    (reset : i.nreset = 0) (commit : v964 s i = 1) (env : assumes s i)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : RegisterTasks s i := by
  by_cases rd_zero : v701 s i = 0
  · exact register_tasks_rd_zero s i agree reset commit rd_zero
  · apply register_tasks_of_written_value s i agree reset commit
    have ctrl := control_values_at_commit s i control reset commit
    have sel := ctrl.write_select.trans (add_write_select _ known)
    have enabled := ctrl.write_enable.trans (add_write_enable _ known)
    rw [dut_alu_written_value s i reset (environment_no_trap s i reset env) sel enabled rd_zero,
      reference_add_written_value s i reset commit known rd_zero]
    exact aligned_reference_arithmetic_add s i alu agree zero commit known
#print axioms register_tasks_add_commit
theorem register_tasks_sub_commit (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (control : ControlAligned s)
    (alu : DecodedAluAligned s) (zero : ReferenceZero s)
    (reset : i.nreset = 0) (commit : v964 s i = 1) (env : assumes s i)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) : RegisterTasks s i := by
  by_cases rd_zero : v701 s i = 0
  · exact register_tasks_rd_zero s i agree reset commit rd_zero
  · apply register_tasks_of_written_value s i agree reset commit
    have ctrl := control_values_at_commit s i control reset commit
    have sel := ctrl.write_select.trans (sub_write_select _ known)
    have enabled := ctrl.write_enable.trans (sub_write_enable _ known)
    rw [dut_alu_written_value s i reset (environment_no_trap s i reset env) sel enabled rd_zero,
      reference_sub_written_value s i reset commit known rd_zero]
    exact aligned_reference_arithmetic_sub s i alu agree zero commit known
#print axioms register_tasks_sub_commit
theorem register_tasks_sll_commit (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (control : ControlAligned s)
    (alu : DecodedAluAligned s) (zero : ReferenceZero s)
    (reset : i.nreset = 0) (commit : v964 s i = 1) (env : assumes s i)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) : RegisterTasks s i := by
  by_cases rd_zero : v701 s i = 0
  · exact register_tasks_rd_zero s i agree reset commit rd_zero
  · apply register_tasks_of_written_value s i agree reset commit
    have ctrl := control_values_at_commit s i control reset commit
    have sel := ctrl.write_select.trans (sll_write_select _ known)
    have enabled := ctrl.write_enable.trans (sll_write_enable _ known)
    rw [dut_alu_written_value s i reset (environment_no_trap s i reset env) sel enabled rd_zero,
      reference_sll_written_value s i reset commit known rd_zero]
    exact aligned_reference_arithmetic_sll s i alu agree zero commit known
#print axioms register_tasks_sll_commit
theorem register_tasks_slt_commit (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (control : ControlAligned s)
    (alu : DecodedAluAligned s) (zero : ReferenceZero s)
    (reset : i.nreset = 0) (commit : v964 s i = 1) (env : assumes s i)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : RegisterTasks s i := by
  by_cases rd_zero : v701 s i = 0
  · exact register_tasks_rd_zero s i agree reset commit rd_zero
  · apply register_tasks_of_written_value s i agree reset commit
    have ctrl := control_values_at_commit s i control reset commit
    have sel := ctrl.write_select.trans (slt_write_select _ known)
    have enabled := ctrl.write_enable.trans (slt_write_enable _ known)
    rw [dut_alu_written_value s i reset (environment_no_trap s i reset env) sel enabled rd_zero,
      reference_slt_written_value s i reset commit known rd_zero]
    exact aligned_reference_arithmetic_slt s i alu agree zero commit known
#print axioms register_tasks_slt_commit
theorem register_tasks_sltu_commit (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (control : ControlAligned s)
    (alu : DecodedAluAligned s) (zero : ReferenceZero s)
    (reset : i.nreset = 0) (commit : v964 s i = 1) (env : assumes s i)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : RegisterTasks s i := by
  by_cases rd_zero : v701 s i = 0
  · exact register_tasks_rd_zero s i agree reset commit rd_zero
  · apply register_tasks_of_written_value s i agree reset commit
    have ctrl := control_values_at_commit s i control reset commit
    have sel := ctrl.write_select.trans (sltu_write_select _ known)
    have enabled := ctrl.write_enable.trans (sltu_write_enable _ known)
    rw [dut_alu_written_value s i reset (environment_no_trap s i reset env) sel enabled rd_zero,
      reference_sltu_written_value s i reset commit known rd_zero]
    exact aligned_reference_arithmetic_sltu s i alu agree zero commit known
#print axioms register_tasks_sltu_commit
theorem register_tasks_xor_commit (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (control : ControlAligned s)
    (alu : DecodedAluAligned s) (zero : ReferenceZero s)
    (reset : i.nreset = 0) (commit : v964 s i = 1) (env : assumes s i)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) : RegisterTasks s i := by
  by_cases rd_zero : v701 s i = 0
  · exact register_tasks_rd_zero s i agree reset commit rd_zero
  · apply register_tasks_of_written_value s i agree reset commit
    have ctrl := control_values_at_commit s i control reset commit
    have sel := ctrl.write_select.trans (xor_write_select _ known)
    have enabled := ctrl.write_enable.trans (xor_write_enable _ known)
    rw [dut_alu_written_value s i reset (environment_no_trap s i reset env) sel enabled rd_zero,
      reference_xor_written_value s i reset commit known rd_zero]
    exact aligned_reference_arithmetic_xor s i alu agree zero commit known
#print axioms register_tasks_xor_commit
theorem register_tasks_srl_commit (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (control : ControlAligned s)
    (alu : DecodedAluAligned s) (zero : ReferenceZero s)
    (reset : i.nreset = 0) (commit : v964 s i = 1) (env : assumes s i)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) : RegisterTasks s i := by
  by_cases rd_zero : v701 s i = 0
  · exact register_tasks_rd_zero s i agree reset commit rd_zero
  · apply register_tasks_of_written_value s i agree reset commit
    have ctrl := control_values_at_commit s i control reset commit
    have sel := ctrl.write_select.trans (srl_write_select _ known)
    have enabled := ctrl.write_enable.trans (srl_write_enable _ known)
    rw [dut_alu_written_value s i reset (environment_no_trap s i reset env) sel enabled rd_zero,
      reference_srl_written_value s i reset commit known rd_zero]
    exact aligned_reference_arithmetic_srl s i alu agree zero commit known
#print axioms register_tasks_srl_commit
theorem register_tasks_sra_commit (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (control : ControlAligned s)
    (alu : DecodedAluAligned s) (zero : ReferenceZero s)
    (reset : i.nreset = 0) (commit : v964 s i = 1) (env : assumes s i)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) : RegisterTasks s i := by
  by_cases rd_zero : v701 s i = 0
  · exact register_tasks_rd_zero s i agree reset commit rd_zero
  · apply register_tasks_of_written_value s i agree reset commit
    have ctrl := control_values_at_commit s i control reset commit
    have sel := ctrl.write_select.trans (sra_write_select _ known)
    have enabled := ctrl.write_enable.trans (sra_write_enable _ known)
    rw [dut_alu_written_value s i reset (environment_no_trap s i reset env) sel enabled rd_zero,
      reference_sra_written_value s i reset commit known rd_zero]
    exact aligned_reference_arithmetic_sra s i alu agree zero commit known
#print axioms register_tasks_sra_commit
theorem register_tasks_or_commit (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (control : ControlAligned s)
    (alu : DecodedAluAligned s) (zero : ReferenceZero s)
    (reset : i.nreset = 0) (commit : v964 s i = 1) (env : assumes s i)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) : RegisterTasks s i := by
  by_cases rd_zero : v701 s i = 0
  · exact register_tasks_rd_zero s i agree reset commit rd_zero
  · apply register_tasks_of_written_value s i agree reset commit
    have ctrl := control_values_at_commit s i control reset commit
    have sel := ctrl.write_select.trans (or_write_select _ known)
    have enabled := ctrl.write_enable.trans (or_write_enable _ known)
    rw [dut_alu_written_value s i reset (environment_no_trap s i reset env) sel enabled rd_zero,
      reference_or_written_value s i reset commit known rd_zero]
    exact aligned_reference_arithmetic_or s i alu agree zero commit known
#print axioms register_tasks_or_commit
theorem register_tasks_and_commit (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (control : ControlAligned s)
    (alu : DecodedAluAligned s) (zero : ReferenceZero s)
    (reset : i.nreset = 0) (commit : v964 s i = 1) (env : assumes s i)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) : RegisterTasks s i := by
  by_cases rd_zero : v701 s i = 0
  · exact register_tasks_rd_zero s i agree reset commit rd_zero
  · apply register_tasks_of_written_value s i agree reset commit
    have ctrl := control_values_at_commit s i control reset commit
    have sel := ctrl.write_select.trans (and_write_select _ known)
    have enabled := ctrl.write_enable.trans (and_write_enable _ known)
    rw [dut_alu_written_value s i reset (environment_no_trap s i reset env) sel enabled rd_zero,
      reference_and_written_value s i reset commit known rd_zero]
    exact aligned_reference_arithmetic_and s i alu agree zero commit known
#print axioms register_tasks_and_commit
def RegisterArithmeticInstruction (instruction : BitVec 32) : Prop :=
  instruction &&& 4261441663 = 51 ∨
  instruction &&& 4261441663 = 1073741875 ∨
  instruction &&& 4261441663 = 4147 ∨
  instruction &&& 4261441663 = 8243 ∨
  instruction &&& 4261441663 = 12339 ∨
  instruction &&& 4261441663 = 16435 ∨
  instruction &&& 4261441663 = 20531 ∨
  instruction &&& 4261441663 = 1073762355 ∨
  instruction &&& 4261441663 = 24627 ∨
  instruction &&& 4261441663 = 28723
theorem register_arithmetic_tasks_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (instruction : RegisterArithmeticInstruction
      (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) :
    RegisterTasks (run initial inputs t) (inputs t) := by
  have control := control_alignment_reachable initial inputs cycles reset env t ht
  have alu := decoded_alu_alignment_reachable initial inputs cycles reset env t ht
  have zero := reference_zero_reachable initial inputs cycles reset t ht
  rcases instruction with known | known | known | known | known | known | known | known | known | known
  · exact register_tasks_add_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
  · exact register_tasks_sub_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
  · exact register_tasks_sll_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
  · exact register_tasks_slt_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
  · exact register_tasks_sltu_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
  · exact register_tasks_xor_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
  · exact register_tasks_srl_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
  · exact register_tasks_sra_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
  · exact register_tasks_or_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
  · exact register_tasks_and_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
#print axioms register_arithmetic_tasks_reachable
end RiscvMiniProofs
