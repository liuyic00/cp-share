import Proofs.PcSuccessor
import Proofs.LoadPc
import Proofs.StoreAddress
namespace RiscvMiniProofs
open nCoreSoc
theorem lui_reference_successor (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      writebackNextPc (run initial inputs t) := by
  have checked := pc_check_alignment_reachable initial inputs cycles reset env t ht
  have checkZero : (run initial inputs t).g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = 0 :=
    checked.trans (decoded_check_lui _ _ _ known)
  have pcEq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
      v2222 (run initial inputs t) (inputs t) := pc
  simp only [writebackNextPc, checkZero, BitVec.reduceEq, ↓reduceIte, pcEq]
  exact reference_lui_next_pc _ _ (reset.2.2 t ht) commit known
#print axioms lui_reference_successor
theorem auipc_reference_successor (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      writebackNextPc (run initial inputs t) := by
  have checked := pc_check_alignment_reachable initial inputs cycles reset env t ht
  have checkZero : (run initial inputs t).g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = 0 :=
    checked.trans (decoded_check_auipc _ _ _ known)
  have pcEq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
      v2222 (run initial inputs t) (inputs t) := pc
  simp only [writebackNextPc, checkZero, BitVec.reduceEq, ↓reduceIte, pcEq]
  exact reference_auipc_next_pc _ _ (reset.2.2 t ht) commit known
#print axioms auipc_reference_successor
theorem lb_reference_successor (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      writebackNextPc (run initial inputs t) := by
  have checked := pc_check_alignment_reachable initial inputs cycles reset env t ht
  have checkZero : (run initial inputs t).g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = 0 :=
    checked.trans (decoded_check_lb _ _ _ known)
  have pcEq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
      v2222 (run initial inputs t) (inputs t) := pc
  simp only [writebackNextPc, checkZero, BitVec.reduceEq, ↓reduceIte, pcEq]
  exact reference_lb_next_pc _ _ (reset.2.2 t ht) commit known
#print axioms lb_reference_successor
theorem lh_reference_successor (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      writebackNextPc (run initial inputs t) := by
  have checked := pc_check_alignment_reachable initial inputs cycles reset env t ht
  have checkZero : (run initial inputs t).g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = 0 :=
    checked.trans (decoded_check_lh _ _ _ known)
  have pcEq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
      v2222 (run initial inputs t) (inputs t) := pc
  simp only [writebackNextPc, checkZero, BitVec.reduceEq, ↓reduceIte, pcEq]
  exact (lh_event_and_pc_reachable initial inputs cycles reset env t ht agree commit known).2
#print axioms lh_reference_successor
theorem lw_reference_successor (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      writebackNextPc (run initial inputs t) := by
  have checked := pc_check_alignment_reachable initial inputs cycles reset env t ht
  have checkZero : (run initial inputs t).g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = 0 :=
    checked.trans (decoded_check_lw _ _ _ known)
  have pcEq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
      v2222 (run initial inputs t) (inputs t) := pc
  simp only [writebackNextPc, checkZero, BitVec.reduceEq, ↓reduceIte, pcEq]
  exact (lw_event_and_pc_reachable initial inputs cycles reset env t ht agree commit known).2
#print axioms lw_reference_successor
theorem lbu_reference_successor (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      writebackNextPc (run initial inputs t) := by
  have checked := pc_check_alignment_reachable initial inputs cycles reset env t ht
  have checkZero : (run initial inputs t).g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = 0 :=
    checked.trans (decoded_check_lbu _ _ _ known)
  have pcEq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
      v2222 (run initial inputs t) (inputs t) := pc
  simp only [writebackNextPc, checkZero, BitVec.reduceEq, ↓reduceIte, pcEq]
  exact reference_lbu_next_pc _ _ (reset.2.2 t ht) commit known
#print axioms lbu_reference_successor
theorem lhu_reference_successor (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      writebackNextPc (run initial inputs t) := by
  have checked := pc_check_alignment_reachable initial inputs cycles reset env t ht
  have checkZero : (run initial inputs t).g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = 0 :=
    checked.trans (decoded_check_lhu _ _ _ known)
  have pcEq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
      v2222 (run initial inputs t) (inputs t) := pc
  simp only [writebackNextPc, checkZero, BitVec.reduceEq, ↓reduceIte, pcEq]
  exact (lhu_event_and_pc_reachable initial inputs cycles reset env t ht agree commit known).2
#print axioms lhu_reference_successor
theorem sb_reference_successor (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      writebackNextPc (run initial inputs t) := by
  have checked := pc_check_alignment_reachable initial inputs cycles reset env t ht
  have checkZero : (run initial inputs t).g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = 0 :=
    checked.trans (decoded_check_sb _ _ _ known)
  have pcEq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
      v2222 (run initial inputs t) (inputs t) := pc
  simp only [writebackNextPc, checkZero, BitVec.reduceEq, ↓reduceIte, pcEq]
  exact reference_sb_next_pc _ _ (reset.2.2 t ht) commit known
#print axioms sb_reference_successor
theorem sh_reference_successor (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      writebackNextPc (run initial inputs t) := by
  have checked := pc_check_alignment_reachable initial inputs cycles reset env t ht
  have checkZero : (run initial inputs t).g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = 0 :=
    checked.trans (decoded_check_sh _ _ _ known)
  have pcEq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
      v2222 (run initial inputs t) (inputs t) := pc
  simp only [writebackNextPc, checkZero, BitVec.reduceEq, ↓reduceIte, pcEq]
  exact (sh_event_and_pc_reachable initial inputs cycles reset env t ht agree commit known).2
#print axioms sh_reference_successor
theorem sw_reference_successor (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      writebackNextPc (run initial inputs t) := by
  have checked := pc_check_alignment_reachable initial inputs cycles reset env t ht
  have checkZero : (run initial inputs t).g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = 0 :=
    checked.trans (decoded_check_sw _ _ _ known)
  have pcEq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
      v2222 (run initial inputs t) (inputs t) := pc
  simp only [writebackNextPc, checkZero, BitVec.reduceEq, ↓reduceIte, pcEq]
  exact (sw_event_and_pc_reachable initial inputs cycles reset env t ht agree commit known).2
#print axioms sw_reference_successor
theorem addi_reference_successor (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      writebackNextPc (run initial inputs t) := by
  have checked := pc_check_alignment_reachable initial inputs cycles reset env t ht
  have checkZero : (run initial inputs t).g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = 0 :=
    checked.trans (decoded_check_addi _ _ _ known)
  have pcEq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
      v2222 (run initial inputs t) (inputs t) := pc
  simp only [writebackNextPc, checkZero, BitVec.reduceEq, ↓reduceIte, pcEq]
  exact reference_addi_next_pc _ _ (reset.2.2 t ht) commit known
#print axioms addi_reference_successor
theorem slti_reference_successor (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      writebackNextPc (run initial inputs t) := by
  have checked := pc_check_alignment_reachable initial inputs cycles reset env t ht
  have checkZero : (run initial inputs t).g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = 0 :=
    checked.trans (decoded_check_slti _ _ _ known)
  have pcEq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
      v2222 (run initial inputs t) (inputs t) := pc
  simp only [writebackNextPc, checkZero, BitVec.reduceEq, ↓reduceIte, pcEq]
  exact reference_slti_next_pc _ _ (reset.2.2 t ht) commit known
#print axioms slti_reference_successor
theorem sltiu_reference_successor (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      writebackNextPc (run initial inputs t) := by
  have checked := pc_check_alignment_reachable initial inputs cycles reset env t ht
  have checkZero : (run initial inputs t).g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = 0 :=
    checked.trans (decoded_check_sltiu _ _ _ known)
  have pcEq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
      v2222 (run initial inputs t) (inputs t) := pc
  simp only [writebackNextPc, checkZero, BitVec.reduceEq, ↓reduceIte, pcEq]
  exact reference_sltiu_next_pc _ _ (reset.2.2 t ht) commit known
#print axioms sltiu_reference_successor
theorem xori_reference_successor (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      writebackNextPc (run initial inputs t) := by
  have checked := pc_check_alignment_reachable initial inputs cycles reset env t ht
  have checkZero : (run initial inputs t).g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = 0 :=
    checked.trans (decoded_check_xori _ _ _ known)
  have pcEq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
      v2222 (run initial inputs t) (inputs t) := pc
  simp only [writebackNextPc, checkZero, BitVec.reduceEq, ↓reduceIte, pcEq]
  exact reference_xori_next_pc _ _ (reset.2.2 t ht) commit known
#print axioms xori_reference_successor
theorem ori_reference_successor (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      writebackNextPc (run initial inputs t) := by
  have checked := pc_check_alignment_reachable initial inputs cycles reset env t ht
  have checkZero : (run initial inputs t).g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = 0 :=
    checked.trans (decoded_check_ori _ _ _ known)
  have pcEq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
      v2222 (run initial inputs t) (inputs t) := pc
  simp only [writebackNextPc, checkZero, BitVec.reduceEq, ↓reduceIte, pcEq]
  exact reference_ori_next_pc _ _ (reset.2.2 t ht) commit known
#print axioms ori_reference_successor
theorem andi_reference_successor (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      writebackNextPc (run initial inputs t) := by
  have checked := pc_check_alignment_reachable initial inputs cycles reset env t ht
  have checkZero : (run initial inputs t).g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = 0 :=
    checked.trans (decoded_check_andi _ _ _ known)
  have pcEq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
      v2222 (run initial inputs t) (inputs t) := pc
  simp only [writebackNextPc, checkZero, BitVec.reduceEq, ↓reduceIte, pcEq]
  exact reference_andi_next_pc _ _ (reset.2.2 t ht) commit known
#print axioms andi_reference_successor
theorem slli_reference_successor (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      writebackNextPc (run initial inputs t) := by
  have checked := pc_check_alignment_reachable initial inputs cycles reset env t ht
  have checkZero : (run initial inputs t).g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = 0 :=
    checked.trans (decoded_check_slli _ _ _ known)
  have pcEq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
      v2222 (run initial inputs t) (inputs t) := pc
  simp only [writebackNextPc, checkZero, BitVec.reduceEq, ↓reduceIte, pcEq]
  exact reference_slli_next_pc _ _ (reset.2.2 t ht) commit known
#print axioms slli_reference_successor
theorem srli_reference_successor (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      writebackNextPc (run initial inputs t) := by
  have checked := pc_check_alignment_reachable initial inputs cycles reset env t ht
  have checkZero : (run initial inputs t).g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = 0 :=
    checked.trans (decoded_check_srli _ _ _ known)
  have pcEq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
      v2222 (run initial inputs t) (inputs t) := pc
  simp only [writebackNextPc, checkZero, BitVec.reduceEq, ↓reduceIte, pcEq]
  exact reference_srli_next_pc _ _ (reset.2.2 t ht) commit known
#print axioms srli_reference_successor
theorem srai_reference_successor (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      writebackNextPc (run initial inputs t) := by
  have checked := pc_check_alignment_reachable initial inputs cycles reset env t ht
  have checkZero : (run initial inputs t).g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = 0 :=
    checked.trans (decoded_check_srai _ _ _ known)
  have pcEq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
      v2222 (run initial inputs t) (inputs t) := pc
  simp only [writebackNextPc, checkZero, BitVec.reduceEq, ↓reduceIte, pcEq]
  exact reference_srai_next_pc _ _ (reset.2.2 t ht) commit known
#print axioms srai_reference_successor
theorem add_reference_successor (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      writebackNextPc (run initial inputs t) := by
  have checked := pc_check_alignment_reachable initial inputs cycles reset env t ht
  have checkZero : (run initial inputs t).g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = 0 :=
    checked.trans (decoded_check_add _ _ _ known)
  have pcEq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
      v2222 (run initial inputs t) (inputs t) := pc
  simp only [writebackNextPc, checkZero, BitVec.reduceEq, ↓reduceIte, pcEq]
  exact reference_add_next_pc _ _ (reset.2.2 t ht) commit known
#print axioms add_reference_successor
theorem sub_reference_successor (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      writebackNextPc (run initial inputs t) := by
  have checked := pc_check_alignment_reachable initial inputs cycles reset env t ht
  have checkZero : (run initial inputs t).g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = 0 :=
    checked.trans (decoded_check_sub _ _ _ known)
  have pcEq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
      v2222 (run initial inputs t) (inputs t) := pc
  simp only [writebackNextPc, checkZero, BitVec.reduceEq, ↓reduceIte, pcEq]
  exact reference_sub_next_pc _ _ (reset.2.2 t ht) commit known
#print axioms sub_reference_successor
theorem sll_reference_successor (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      writebackNextPc (run initial inputs t) := by
  have checked := pc_check_alignment_reachable initial inputs cycles reset env t ht
  have checkZero : (run initial inputs t).g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = 0 :=
    checked.trans (decoded_check_sll _ _ _ known)
  have pcEq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
      v2222 (run initial inputs t) (inputs t) := pc
  simp only [writebackNextPc, checkZero, BitVec.reduceEq, ↓reduceIte, pcEq]
  exact reference_sll_next_pc _ _ (reset.2.2 t ht) commit known
#print axioms sll_reference_successor
theorem slt_reference_successor (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      writebackNextPc (run initial inputs t) := by
  have checked := pc_check_alignment_reachable initial inputs cycles reset env t ht
  have checkZero : (run initial inputs t).g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = 0 :=
    checked.trans (decoded_check_slt _ _ _ known)
  have pcEq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
      v2222 (run initial inputs t) (inputs t) := pc
  simp only [writebackNextPc, checkZero, BitVec.reduceEq, ↓reduceIte, pcEq]
  exact reference_slt_next_pc _ _ (reset.2.2 t ht) commit known
#print axioms slt_reference_successor
theorem sltu_reference_successor (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      writebackNextPc (run initial inputs t) := by
  have checked := pc_check_alignment_reachable initial inputs cycles reset env t ht
  have checkZero : (run initial inputs t).g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = 0 :=
    checked.trans (decoded_check_sltu _ _ _ known)
  have pcEq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
      v2222 (run initial inputs t) (inputs t) := pc
  simp only [writebackNextPc, checkZero, BitVec.reduceEq, ↓reduceIte, pcEq]
  exact reference_sltu_next_pc _ _ (reset.2.2 t ht) commit known
#print axioms sltu_reference_successor
theorem xor_reference_successor (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      writebackNextPc (run initial inputs t) := by
  have checked := pc_check_alignment_reachable initial inputs cycles reset env t ht
  have checkZero : (run initial inputs t).g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = 0 :=
    checked.trans (decoded_check_xor _ _ _ known)
  have pcEq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
      v2222 (run initial inputs t) (inputs t) := pc
  simp only [writebackNextPc, checkZero, BitVec.reduceEq, ↓reduceIte, pcEq]
  exact reference_xor_next_pc _ _ (reset.2.2 t ht) commit known
#print axioms xor_reference_successor
theorem srl_reference_successor (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      writebackNextPc (run initial inputs t) := by
  have checked := pc_check_alignment_reachable initial inputs cycles reset env t ht
  have checkZero : (run initial inputs t).g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = 0 :=
    checked.trans (decoded_check_srl _ _ _ known)
  have pcEq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
      v2222 (run initial inputs t) (inputs t) := pc
  simp only [writebackNextPc, checkZero, BitVec.reduceEq, ↓reduceIte, pcEq]
  exact reference_srl_next_pc _ _ (reset.2.2 t ht) commit known
#print axioms srl_reference_successor
theorem sra_reference_successor (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      writebackNextPc (run initial inputs t) := by
  have checked := pc_check_alignment_reachable initial inputs cycles reset env t ht
  have checkZero : (run initial inputs t).g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = 0 :=
    checked.trans (decoded_check_sra _ _ _ known)
  have pcEq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
      v2222 (run initial inputs t) (inputs t) := pc
  simp only [writebackNextPc, checkZero, BitVec.reduceEq, ↓reduceIte, pcEq]
  exact reference_sra_next_pc _ _ (reset.2.2 t ht) commit known
#print axioms sra_reference_successor
theorem or_reference_successor (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      writebackNextPc (run initial inputs t) := by
  have checked := pc_check_alignment_reachable initial inputs cycles reset env t ht
  have checkZero : (run initial inputs t).g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = 0 :=
    checked.trans (decoded_check_or _ _ _ known)
  have pcEq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
      v2222 (run initial inputs t) (inputs t) := pc
  simp only [writebackNextPc, checkZero, BitVec.reduceEq, ↓reduceIte, pcEq]
  exact reference_or_next_pc _ _ (reset.2.2 t ht) commit known
#print axioms or_reference_successor
theorem and_reference_successor (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      writebackNextPc (run initial inputs t) := by
  have checked := pc_check_alignment_reachable initial inputs cycles reset env t ht
  have checkZero : (run initial inputs t).g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = 0 :=
    checked.trans (decoded_check_and _ _ _ known)
  have pcEq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
      v2222 (run initial inputs t) (inputs t) := pc
  simp only [writebackNextPc, checkZero, BitVec.reduceEq, ↓reduceIte, pcEq]
  exact reference_and_next_pc _ _ (reset.2.2 t ht) commit known
#print axioms and_reference_successor
end RiscvMiniProofs
