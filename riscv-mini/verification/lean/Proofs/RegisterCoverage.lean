import Proofs.SupportedInstructions
import Proofs.ImmediateCommit
import Proofs.UpperCommit
import Proofs.NonwritingCommit
import Proofs.JalAlignment
import Proofs.JalrAlignment
namespace RiscvMiniProofs
open nCoreSoc
inductive LoadInstruction (instruction : BitVec 32) : Prop where
  | op_lb : instruction &&& 28799 = 3 → LoadInstruction instruction
  | op_lh : instruction &&& 28799 = 4099 → LoadInstruction instruction
  | op_lw : instruction &&& 28799 = 8195 → LoadInstruction instruction
  | op_lbu : instruction &&& 28799 = 16387 → LoadInstruction instruction
  | op_lhu : instruction &&& 28799 = 20483 → LoadInstruction instruction

-- Reduction of original tasks, not an added environment assumption or a proof
-- of the load-value/PC premises. Entry register agreement is still required.
theorem register_tasks_reachable_of_pc_and_loads (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (pc : WritebackPcAgreement (run initial inputs t))
    (loads : LoadInstruction (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst →
      dutRead (step (run initial inputs t) (inputs t)) (v701 (run initial inputs t) (inputs t)) =
        referenceRead (step (run initial inputs t) (inputs t)) (v701 (run initial inputs t) (inputs t))) :
    RegisterTasks (run initial inputs t) (inputs t) := by
  have control := control_alignment_reachable initial inputs cycles reset env t ht
  have alu := decoded_alu_alignment_reachable initial inputs cycles reset env t ht
  have zero := reference_zero_reachable initial inputs cycles reset t ht
  have supported := environment_supported_at_commit _ _ (reset.2.2 t ht) (env t) commit
  cases supported with
  | op_addi known =>
    exact register_tasks_addi_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
  | op_slti known =>
    exact register_tasks_slti_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
  | op_sltiu known =>
    exact register_tasks_sltiu_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
  | op_andi known =>
    exact register_tasks_andi_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
  | op_ori known =>
    exact register_tasks_ori_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
  | op_xori known =>
    exact register_tasks_xori_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
  | op_slli known =>
    exact register_tasks_slli_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
  | op_srli known =>
    exact register_tasks_srli_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
  | op_srai known =>
    exact register_tasks_srai_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
  | op_lui known =>
    exact register_tasks_lui_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
  | op_auipc known =>
    exact register_tasks_auipc_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) pc known
  | op_add known =>
    exact register_tasks_add_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
  | op_slt known =>
    exact register_tasks_slt_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
  | op_sltu known =>
    exact register_tasks_sltu_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
  | op_and known =>
    exact register_tasks_and_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
  | op_or known =>
    exact register_tasks_or_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
  | op_xor known =>
    exact register_tasks_xor_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
  | op_sll known =>
    exact register_tasks_sll_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
  | op_srl known =>
    exact register_tasks_srl_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
  | op_sub known =>
    exact register_tasks_sub_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
  | op_sra known =>
    exact register_tasks_sra_commit _ _ agree control alu zero (reset.2.2 t ht) commit (env t) known
  | op_jal known =>
    exact jal_tasks_reachable_of_pc initial inputs cycles reset env t ht agree commit pc known
  | op_jalr known =>
    exact jalr_tasks_reachable_of_pc initial inputs cycles reset env t ht agree commit pc known
  | op_beq known =>
    exact register_tasks_beq_commit _ _ agree control (reset.2.2 t ht) commit known
  | op_bne known =>
    exact register_tasks_bne_commit _ _ agree control (reset.2.2 t ht) commit known
  | op_blt known =>
    exact register_tasks_blt_commit _ _ agree control (reset.2.2 t ht) commit known
  | op_bltu known =>
    exact register_tasks_bltu_commit _ _ agree control (reset.2.2 t ht) commit known
  | op_bge known =>
    exact register_tasks_bge_commit _ _ agree control (reset.2.2 t ht) commit known
  | op_bgeu known =>
    exact register_tasks_bgeu_commit _ _ agree control (reset.2.2 t ht) commit known
  | op_lb known =>
    exact register_tasks_of_written_value _ _ agree (reset.2.2 t ht) commit (loads (LoadInstruction.op_lb known))
  | op_lh known =>
    exact register_tasks_of_written_value _ _ agree (reset.2.2 t ht) commit (loads (LoadInstruction.op_lh known))
  | op_lw known =>
    exact register_tasks_of_written_value _ _ agree (reset.2.2 t ht) commit (loads (LoadInstruction.op_lw known))
  | op_lbu known =>
    exact register_tasks_of_written_value _ _ agree (reset.2.2 t ht) commit (loads (LoadInstruction.op_lbu known))
  | op_lhu known =>
    exact register_tasks_of_written_value _ _ agree (reset.2.2 t ht) commit (loads (LoadInstruction.op_lhu known))
  | op_sb known =>
    exact register_tasks_sb_commit _ _ agree control (reset.2.2 t ht) commit known
  | op_sh known =>
    exact register_tasks_sh_commit _ _ agree control (reset.2.2 t ht) commit known
  | op_sw known =>
    exact register_tasks_sw_commit _ _ agree control (reset.2.2 t ht) commit known
#print axioms register_tasks_reachable_of_pc_and_loads
end RiscvMiniProofs
