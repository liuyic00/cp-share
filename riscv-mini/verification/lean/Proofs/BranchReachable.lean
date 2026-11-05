import Proofs.TrapFacts
import Proofs.BranchCompare
import Proofs.PcCheckAlignment
import Proofs.BranchTarget
import Proofs.ReferenceBranchSemantics
import Proofs.PcLowBit
namespace RiscvMiniProofs
open nCoreSoc
private theorem low_two_zero (x : BitVec 32)
    (bit0 : BitVec.extractLsb' 0 1 x = 0) (bit1 : BitVec.extractLsb' 1 1 x = 0) :
    BitVec.extractLsb' 0 2 x = 0 := by
  have b0 := congrArg (fun y : BitVec 1 => y.getLsbD 0) bit0
  have b1 := congrArg (fun y : BitVec 1 => y.getLsbD 0) bit1
  have h0 : x[0] = false := by simpa using b0
  have h1 : x[1] = false := by simpa using b1
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have cases : j = 0 ∨ j = 1 := by omega
  rcases cases with h | h <;> subst j <;> simp [h0, h1]


theorem beq_check_agreement (s : State) (i : Inputs)
    (checked : PcCheckAligned s) (agree : RegisterAgreement s) (zero : ReferenceZero s)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) :
    s.g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = v6665 s i := by
  rw [pc_check_reference_operands s checked agree, decoded_check_beq_semantics _ _ _ known,
    ← reference_beq_operand1 s i zero commit known,
    ← reference_beq_operand2 s i zero commit known]
  rfl

theorem beq_target_aligned_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99)
    (taken : v6665 (run initial inputs t) (inputs t) = 1) :
    BitVec.extractLsb' 0 2 (v2222 (run initial inputs t) (inputs t) +
      v2092 (run initial inputs t) (inputs t)) = 0 := by
  apply low_two_zero
  · rw [beq_target_low_bit _ _ commit known]
    have low := (pc_low_bit_reachable initial inputs cycles reset env t ht).writeback
    have eq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
        v2222 (run initial inputs t) (inputs t) := pc
    rw [eq] at low
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have h : j = 0 := by omega
    subst j
    simpa using low
  · have target := beq_target_agreement _ _
      (decoded_alu_alignment_reachable initial inputs cycles reset env t ht) pc commit known
    rw [← target]
    apply environment_pc_bit _ _ (reset.2.2 t ht) (env t)
    exact (beq_check_agreement _ _
      (pc_check_alignment_reachable initial inputs cycles reset env t ht) agree
      (reference_zero_reachable initial inputs cycles reset t ht) commit known).trans taken

theorem beq_event_and_pc_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) :
    TaskHolds ⟨40, by decide⟩ (run initial inputs t) (inputs t) ∧
      (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
        if v6665 (run initial inputs t) (inputs t) = 1 then
          v2222 (run initial inputs t) (inputs t) + v2092 (run initial inputs t) (inputs t)
        else v2222 (run initial inputs t) (inputs t) + 4 := by
  exact reference_beq_event_and_pc _ _ (reset.2.2 t ht) (env t)
    (reference_config_reachable initial inputs cycles reset t ht) commit known
    (beq_target_aligned_reachable initial inputs cycles reset env t ht agree pc commit known)
#print axioms beq_event_and_pc_reachable

theorem bne_check_agreement (s : State) (i : Inputs)
    (checked : PcCheckAligned s) (agree : RegisterAgreement s) (zero : ReferenceZero s)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) :
    s.g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = v6641 s i := by
  rw [pc_check_reference_operands s checked agree, decoded_check_bne_semantics _ _ _ known,
    ← reference_bne_operand1 s i zero commit known,
    ← reference_bne_operand2 s i zero commit known]
  rfl

theorem bne_target_aligned_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195)
    (taken : v6641 (run initial inputs t) (inputs t) = 1) :
    BitVec.extractLsb' 0 2 (v2222 (run initial inputs t) (inputs t) +
      v2092 (run initial inputs t) (inputs t)) = 0 := by
  apply low_two_zero
  · rw [bne_target_low_bit _ _ commit known]
    have low := (pc_low_bit_reachable initial inputs cycles reset env t ht).writeback
    have eq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
        v2222 (run initial inputs t) (inputs t) := pc
    rw [eq] at low
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have h : j = 0 := by omega
    subst j
    simpa using low
  · have target := bne_target_agreement _ _
      (decoded_alu_alignment_reachable initial inputs cycles reset env t ht) pc commit known
    rw [← target]
    apply environment_pc_bit _ _ (reset.2.2 t ht) (env t)
    exact (bne_check_agreement _ _
      (pc_check_alignment_reachable initial inputs cycles reset env t ht) agree
      (reference_zero_reachable initial inputs cycles reset t ht) commit known).trans taken

theorem bne_event_and_pc_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) :
    TaskHolds ⟨40, by decide⟩ (run initial inputs t) (inputs t) ∧
      (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
        if v6641 (run initial inputs t) (inputs t) = 1 then
          v2222 (run initial inputs t) (inputs t) + v2092 (run initial inputs t) (inputs t)
        else v2222 (run initial inputs t) (inputs t) + 4 := by
  exact reference_bne_event_and_pc _ _ (reset.2.2 t ht) (env t)
    (reference_config_reachable initial inputs cycles reset t ht) commit known
    (bne_target_aligned_reachable initial inputs cycles reset env t ht agree pc commit known)
#print axioms bne_event_and_pc_reachable

theorem blt_check_agreement (s : State) (i : Inputs)
    (checked : PcCheckAligned s) (agree : RegisterAgreement s) (zero : ReferenceZero s)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) :
    s.g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = v6617 s i := by
  rw [pc_check_reference_operands s checked agree, decoded_check_blt_semantics _ _ _ known,
    ← reference_blt_operand1 s i zero commit known,
    ← reference_blt_operand2 s i zero commit known]
  rfl

theorem blt_target_aligned_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483)
    (taken : v6617 (run initial inputs t) (inputs t) = 1) :
    BitVec.extractLsb' 0 2 (v2222 (run initial inputs t) (inputs t) +
      v2092 (run initial inputs t) (inputs t)) = 0 := by
  apply low_two_zero
  · rw [blt_target_low_bit _ _ commit known]
    have low := (pc_low_bit_reachable initial inputs cycles reset env t ht).writeback
    have eq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
        v2222 (run initial inputs t) (inputs t) := pc
    rw [eq] at low
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have h : j = 0 := by omega
    subst j
    simpa using low
  · have target := blt_target_agreement _ _
      (decoded_alu_alignment_reachable initial inputs cycles reset env t ht) pc commit known
    rw [← target]
    apply environment_pc_bit _ _ (reset.2.2 t ht) (env t)
    exact (blt_check_agreement _ _
      (pc_check_alignment_reachable initial inputs cycles reset env t ht) agree
      (reference_zero_reachable initial inputs cycles reset t ht) commit known).trans taken

theorem blt_event_and_pc_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) :
    TaskHolds ⟨40, by decide⟩ (run initial inputs t) (inputs t) ∧
      (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
        if v6617 (run initial inputs t) (inputs t) = 1 then
          v2222 (run initial inputs t) (inputs t) + v2092 (run initial inputs t) (inputs t)
        else v2222 (run initial inputs t) (inputs t) + 4 := by
  exact reference_blt_event_and_pc _ _ (reset.2.2 t ht) (env t)
    (reference_config_reachable initial inputs cycles reset t ht) commit known
    (blt_target_aligned_reachable initial inputs cycles reset env t ht agree pc commit known)
#print axioms blt_event_and_pc_reachable

theorem bge_check_agreement (s : State) (i : Inputs)
    (checked : PcCheckAligned s) (agree : RegisterAgreement s) (zero : ReferenceZero s)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) :
    s.g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = v6569 s i := by
  rw [pc_check_reference_operands s checked agree, decoded_check_bge_semantics _ _ _ known,
    ← reference_bge_operand1 s i zero commit known,
    ← reference_bge_operand2 s i zero commit known]
  rfl

theorem bge_target_aligned_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579)
    (taken : v6569 (run initial inputs t) (inputs t) = 1) :
    BitVec.extractLsb' 0 2 (v2222 (run initial inputs t) (inputs t) +
      v2092 (run initial inputs t) (inputs t)) = 0 := by
  apply low_two_zero
  · rw [bge_target_low_bit _ _ commit known]
    have low := (pc_low_bit_reachable initial inputs cycles reset env t ht).writeback
    have eq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
        v2222 (run initial inputs t) (inputs t) := pc
    rw [eq] at low
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have h : j = 0 := by omega
    subst j
    simpa using low
  · have target := bge_target_agreement _ _
      (decoded_alu_alignment_reachable initial inputs cycles reset env t ht) pc commit known
    rw [← target]
    apply environment_pc_bit _ _ (reset.2.2 t ht) (env t)
    exact (bge_check_agreement _ _
      (pc_check_alignment_reachable initial inputs cycles reset env t ht) agree
      (reference_zero_reachable initial inputs cycles reset t ht) commit known).trans taken

theorem bge_event_and_pc_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) :
    TaskHolds ⟨40, by decide⟩ (run initial inputs t) (inputs t) ∧
      (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
        if v6569 (run initial inputs t) (inputs t) = 1 then
          v2222 (run initial inputs t) (inputs t) + v2092 (run initial inputs t) (inputs t)
        else v2222 (run initial inputs t) (inputs t) + 4 := by
  exact reference_bge_event_and_pc _ _ (reset.2.2 t ht) (env t)
    (reference_config_reachable initial inputs cycles reset t ht) commit known
    (bge_target_aligned_reachable initial inputs cycles reset env t ht agree pc commit known)
#print axioms bge_event_and_pc_reachable

theorem bltu_check_agreement (s : State) (i : Inputs)
    (checked : PcCheckAligned s) (agree : RegisterAgreement s) (zero : ReferenceZero s)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) :
    s.g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = v6593 s i := by
  rw [pc_check_reference_operands s checked agree, decoded_check_bltu_semantics _ _ _ known,
    ← reference_bltu_operand1 s i zero commit known,
    ← reference_bltu_operand2 s i zero commit known]
  rfl

theorem bltu_target_aligned_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675)
    (taken : v6593 (run initial inputs t) (inputs t) = 1) :
    BitVec.extractLsb' 0 2 (v2222 (run initial inputs t) (inputs t) +
      v2092 (run initial inputs t) (inputs t)) = 0 := by
  apply low_two_zero
  · rw [bltu_target_low_bit _ _ commit known]
    have low := (pc_low_bit_reachable initial inputs cycles reset env t ht).writeback
    have eq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
        v2222 (run initial inputs t) (inputs t) := pc
    rw [eq] at low
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have h : j = 0 := by omega
    subst j
    simpa using low
  · have target := bltu_target_agreement _ _
      (decoded_alu_alignment_reachable initial inputs cycles reset env t ht) pc commit known
    rw [← target]
    apply environment_pc_bit _ _ (reset.2.2 t ht) (env t)
    exact (bltu_check_agreement _ _
      (pc_check_alignment_reachable initial inputs cycles reset env t ht) agree
      (reference_zero_reachable initial inputs cycles reset t ht) commit known).trans taken

theorem bltu_event_and_pc_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) :
    TaskHolds ⟨40, by decide⟩ (run initial inputs t) (inputs t) ∧
      (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
        if v6593 (run initial inputs t) (inputs t) = 1 then
          v2222 (run initial inputs t) (inputs t) + v2092 (run initial inputs t) (inputs t)
        else v2222 (run initial inputs t) (inputs t) + 4 := by
  exact reference_bltu_event_and_pc _ _ (reset.2.2 t ht) (env t)
    (reference_config_reachable initial inputs cycles reset t ht) commit known
    (bltu_target_aligned_reachable initial inputs cycles reset env t ht agree pc commit known)
#print axioms bltu_event_and_pc_reachable

theorem bgeu_check_agreement (s : State) (i : Inputs)
    (checked : PcCheckAligned s) (agree : RegisterAgreement s) (zero : ReferenceZero s)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) :
    s.g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = v6545 s i := by
  rw [pc_check_reference_operands s checked agree, decoded_check_bgeu_semantics _ _ _ known,
    ← reference_bgeu_operand1 s i zero commit known,
    ← reference_bgeu_operand2 s i zero commit known]
  rfl

theorem bgeu_target_aligned_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771)
    (taken : v6545 (run initial inputs t) (inputs t) = 1) :
    BitVec.extractLsb' 0 2 (v2222 (run initial inputs t) (inputs t) +
      v2092 (run initial inputs t) (inputs t)) = 0 := by
  apply low_two_zero
  · rw [bgeu_target_low_bit _ _ commit known]
    have low := (pc_low_bit_reachable initial inputs cycles reset env t ht).writeback
    have eq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
        v2222 (run initial inputs t) (inputs t) := pc
    rw [eq] at low
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have h : j = 0 := by omega
    subst j
    simpa using low
  · have target := bgeu_target_agreement _ _
      (decoded_alu_alignment_reachable initial inputs cycles reset env t ht) pc commit known
    rw [← target]
    apply environment_pc_bit _ _ (reset.2.2 t ht) (env t)
    exact (bgeu_check_agreement _ _
      (pc_check_alignment_reachable initial inputs cycles reset env t ht) agree
      (reference_zero_reachable initial inputs cycles reset t ht) commit known).trans taken

theorem bgeu_event_and_pc_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) :
    TaskHolds ⟨40, by decide⟩ (run initial inputs t) (inputs t) ∧
      (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
        if v6545 (run initial inputs t) (inputs t) = 1 then
          v2222 (run initial inputs t) (inputs t) + v2092 (run initial inputs t) (inputs t)
        else v2222 (run initial inputs t) (inputs t) + 4 := by
  exact reference_bgeu_event_and_pc _ _ (reset.2.2 t ht) (env t)
    (reference_config_reachable initial inputs cycles reset t ht) commit known
    (bgeu_target_aligned_reachable initial inputs cycles reset env t ht agree pc commit known)
#print axioms bgeu_event_and_pc_reachable

end RiscvMiniProofs
