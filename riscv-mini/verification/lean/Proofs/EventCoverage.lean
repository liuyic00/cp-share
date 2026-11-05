import Proofs.BranchReachable
import Proofs.JumpPc
import Proofs.LoadPc
import Proofs.StoreAddress
import Proofs.RegisterReachability
namespace RiscvMiniProofs
open nCoreSoc

theorem event_valid_reachable_of_pc (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : ValidWritebackPcAgreement (run initial inputs t)) :
    TaskHolds ⟨40, by decide⟩ (run initial inputs t) (inputs t) := by
  rcases BitVec.eq_zero_or_eq_one (v964 (run initial inputs t) (inputs t)) with idle | commit
  · apply (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mpr
    simp [v6727, idle, v4]
  · have currentPc := pc ((commit_iff_valid_writeback _ _ (reset.2.2 t ht)).mp commit)
    have supported := environment_supported_at_commit _ _ (reset.2.2 t ht) (env t) commit
    cases supported with
    | op_addi known =>
      exact reference_addi_event_task _ _ (reset.2.2 t ht) (env t) commit known
    | op_slti known =>
      exact reference_slti_event_task _ _ (reset.2.2 t ht) (env t) commit known
    | op_sltiu known =>
      exact reference_sltiu_event_task _ _ (reset.2.2 t ht) (env t) commit known
    | op_andi known =>
      exact reference_andi_event_task _ _ (reset.2.2 t ht) (env t) commit known
    | op_ori known =>
      exact reference_ori_event_task _ _ (reset.2.2 t ht) (env t) commit known
    | op_xori known =>
      exact reference_xori_event_task _ _ (reset.2.2 t ht) (env t) commit known
    | op_slli known =>
      exact reference_slli_event_task _ _ (reset.2.2 t ht) (env t) commit known
    | op_srli known =>
      exact reference_srli_event_task _ _ (reset.2.2 t ht) (env t) commit known
    | op_srai known =>
      exact reference_srai_event_task _ _ (reset.2.2 t ht) (env t) commit known
    | op_lui known =>
      exact reference_lui_event_task _ _ (reset.2.2 t ht) (env t) commit known
    | op_auipc known =>
      exact reference_auipc_event_task _ _ (reset.2.2 t ht) (env t) commit known
    | op_add known =>
      exact reference_add_event_task _ _ (reset.2.2 t ht) (env t) commit known
    | op_slt known =>
      exact reference_slt_event_task _ _ (reset.2.2 t ht) (env t) commit known
    | op_sltu known =>
      exact reference_sltu_event_task _ _ (reset.2.2 t ht) (env t) commit known
    | op_and known =>
      exact reference_and_event_task _ _ (reset.2.2 t ht) (env t) commit known
    | op_or known =>
      exact reference_or_event_task _ _ (reset.2.2 t ht) (env t) commit known
    | op_xor known =>
      exact reference_xor_event_task _ _ (reset.2.2 t ht) (env t) commit known
    | op_sll known =>
      exact reference_sll_event_task _ _ (reset.2.2 t ht) (env t) commit known
    | op_srl known =>
      exact reference_srl_event_task _ _ (reset.2.2 t ht) (env t) commit known
    | op_sub known =>
      exact reference_sub_event_task _ _ (reset.2.2 t ht) (env t) commit known
    | op_sra known =>
      exact reference_sra_event_task _ _ (reset.2.2 t ht) (env t) commit known
    | op_jal known =>
      exact (jal_event_and_pc_reachable initial inputs cycles reset env t ht currentPc commit known).1
    | op_jalr known =>
      exact (jalr_event_and_pc_reachable initial inputs cycles reset env t ht agree commit known).1
    | op_beq known =>
      exact (beq_event_and_pc_reachable initial inputs cycles reset env t ht agree currentPc commit known).1
    | op_bne known =>
      exact (bne_event_and_pc_reachable initial inputs cycles reset env t ht agree currentPc commit known).1
    | op_blt known =>
      exact (blt_event_and_pc_reachable initial inputs cycles reset env t ht agree currentPc commit known).1
    | op_bltu known =>
      exact (bltu_event_and_pc_reachable initial inputs cycles reset env t ht agree currentPc commit known).1
    | op_bge known =>
      exact (bge_event_and_pc_reachable initial inputs cycles reset env t ht agree currentPc commit known).1
    | op_bgeu known =>
      exact (bgeu_event_and_pc_reachable initial inputs cycles reset env t ht agree currentPc commit known).1
    | op_lb known =>
      exact reference_lb_event_task _ _ (reset.2.2 t ht) (env t) commit known
    | op_lh known =>
      exact (lh_event_and_pc_reachable initial inputs cycles reset env t ht agree commit known).1
    | op_lw known =>
      exact (lw_event_and_pc_reachable initial inputs cycles reset env t ht agree commit known).1
    | op_lbu known =>
      exact reference_lbu_event_task _ _ (reset.2.2 t ht) (env t) commit known
    | op_lhu known =>
      exact (lhu_event_and_pc_reachable initial inputs cycles reset env t ht agree commit known).1
    | op_sb known =>
      exact reference_sb_event_task _ _ (reset.2.2 t ht) (env t) commit known
    | op_sh known =>
      exact (sh_event_and_pc_reachable initial inputs cycles reset env t ht agree commit known).1
    | op_sw known =>
      exact (sw_event_and_pc_reachable initial inputs cycles reset env t ht agree commit known).1

theorem event_valid_reachable_of_pc_trace (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (pc : ∀ t, cycles ≤ t → ValidWritebackPcAgreement (run initial inputs t))
    (t : Nat) (ht : cycles ≤ t) :
    TaskHolds ⟨40, by decide⟩ (run initial inputs t) (inputs t) :=
  event_valid_reachable_of_pc initial inputs cycles reset env t ht
    (registers_agree_reachable_of_pc initial inputs cycles reset env pc t ht) (pc t ht)
#print axioms event_valid_reachable_of_pc
#print axioms event_valid_reachable_of_pc_trace
end RiscvMiniProofs
