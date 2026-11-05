import Proofs.SequentialSuccessor
import Proofs.ControlSuccessor
import Proofs.PcBridge
namespace RiscvMiniProofs
open nCoreSoc

theorem reference_successor_at_commit (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      writebackNextPc (run initial inputs t) := by
  have supported := environment_supported_at_commit _ _ (reset.2.2 t ht) (env t) commit
  cases supported with
  | op_addi known => exact addi_reference_successor initial inputs cycles reset env t ht agree pc commit known
  | op_slti known => exact slti_reference_successor initial inputs cycles reset env t ht agree pc commit known
  | op_sltiu known => exact sltiu_reference_successor initial inputs cycles reset env t ht agree pc commit known
  | op_andi known => exact andi_reference_successor initial inputs cycles reset env t ht agree pc commit known
  | op_ori known => exact ori_reference_successor initial inputs cycles reset env t ht agree pc commit known
  | op_xori known => exact xori_reference_successor initial inputs cycles reset env t ht agree pc commit known
  | op_slli known => exact slli_reference_successor initial inputs cycles reset env t ht agree pc commit known
  | op_srli known => exact srli_reference_successor initial inputs cycles reset env t ht agree pc commit known
  | op_srai known => exact srai_reference_successor initial inputs cycles reset env t ht agree pc commit known
  | op_lui known => exact lui_reference_successor initial inputs cycles reset env t ht agree pc commit known
  | op_auipc known => exact auipc_reference_successor initial inputs cycles reset env t ht agree pc commit known
  | op_add known => exact add_reference_successor initial inputs cycles reset env t ht agree pc commit known
  | op_slt known => exact slt_reference_successor initial inputs cycles reset env t ht agree pc commit known
  | op_sltu known => exact sltu_reference_successor initial inputs cycles reset env t ht agree pc commit known
  | op_and known => exact and_reference_successor initial inputs cycles reset env t ht agree pc commit known
  | op_or known => exact or_reference_successor initial inputs cycles reset env t ht agree pc commit known
  | op_xor known => exact xor_reference_successor initial inputs cycles reset env t ht agree pc commit known
  | op_sll known => exact sll_reference_successor initial inputs cycles reset env t ht agree pc commit known
  | op_srl known => exact srl_reference_successor initial inputs cycles reset env t ht agree pc commit known
  | op_sub known => exact sub_reference_successor initial inputs cycles reset env t ht agree pc commit known
  | op_sra known => exact sra_reference_successor initial inputs cycles reset env t ht agree pc commit known
  | op_jal known => exact jal_reference_successor initial inputs cycles reset env t ht agree pc commit known
  | op_jalr known => exact jalr_reference_successor initial inputs cycles reset env t ht agree pc commit known
  | op_beq known => exact beq_reference_successor initial inputs cycles reset env t ht agree pc commit known
  | op_bne known => exact bne_reference_successor initial inputs cycles reset env t ht agree pc commit known
  | op_blt known => exact blt_reference_successor initial inputs cycles reset env t ht agree pc commit known
  | op_bltu known => exact bltu_reference_successor initial inputs cycles reset env t ht agree pc commit known
  | op_bge known => exact bge_reference_successor initial inputs cycles reset env t ht agree pc commit known
  | op_bgeu known => exact bgeu_reference_successor initial inputs cycles reset env t ht agree pc commit known
  | op_lb known => exact lb_reference_successor initial inputs cycles reset env t ht agree pc commit known
  | op_lh known => exact lh_reference_successor initial inputs cycles reset env t ht agree pc commit known
  | op_lw known => exact lw_reference_successor initial inputs cycles reset env t ht agree pc commit known
  | op_lbu known => exact lbu_reference_successor initial inputs cycles reset env t ht agree pc commit known
  | op_lhu known => exact lhu_reference_successor initial inputs cycles reset env t ht agree pc commit known
  | op_sb known => exact sb_reference_successor initial inputs cycles reset env t ht agree pc commit known
  | op_sh known => exact sh_reference_successor initial inputs cycles reset env t ht agree pc commit known
  | op_sw known => exact sw_reference_successor initial inputs cycles reset env t ht agree pc commit known

theorem reference_pc_step_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : ValidWritebackPcAgreement (run initial inputs t)) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      if v964 (run initial inputs t) (inputs t) = 1 then writebackNextPc (run initial inputs t)
      else (run initial inputs t).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc := by
  by_cases commit : v964 (run initial inputs t) (inputs t) = 1
  · rw [if_pos commit]
    exact reference_successor_at_commit initial inputs cycles reset env t ht agree
      (pc ((commit_iff_valid_writeback _ _ (reset.2.2 t ht)).mp commit)) commit
  · rw [if_neg commit]
    exact reference_pc_idle _ _ (reset.2.2 t ht) commit

#print axioms reference_successor_at_commit
#print axioms reference_pc_step_reachable
end RiscvMiniProofs
