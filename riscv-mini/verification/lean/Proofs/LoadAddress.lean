import Proofs.LoadExecution
import Proofs.ReferenceLoadDecode
import Proofs.ReferenceExecution
import Proofs.RegisterCoverage
namespace RiscvMiniProofs
open nCoreSoc

-- Both sides use the harness's actual memory response; this does not prove
-- the separate original memory-request assertions.
theorem reference_load_response (s : State) (i : Inputs) : v2103 s i = v719 s i := rfl

theorem reference_load_address (s : State) (i : Inputs) :
    v2095 s i = v1721 s i + v2092 s i := by
  change refExec_v2303 (v1721 s i) (v2092 s i) = _
  exact reference_execution_add _ _

theorem load_address_lb (s : State) (i : Inputs)
    (alu : DecodedAluAligned s) (agree : RegisterAgreement s) (zero : ReferenceZero s)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v2095 s i := by
  have value := (decoded_alu_reference_operands s alu agree).trans
    (decoded_execution_lb _ _ _ _ known)
  rw [← reference_lb_operand1 s i zero commit known,
    ← reference_lb_immediate s i commit known] at value
  exact value.trans (reference_load_address s i).symm
#print axioms load_address_lb

theorem load_address_lh (s : State) (i : Inputs)
    (alu : DecodedAluAligned s) (agree : RegisterAgreement s) (zero : ReferenceZero s)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v2095 s i := by
  have value := (decoded_alu_reference_operands s alu agree).trans
    (decoded_execution_lh _ _ _ _ known)
  rw [← reference_lh_operand1 s i zero commit known,
    ← reference_lh_immediate s i commit known] at value
  exact value.trans (reference_load_address s i).symm
#print axioms load_address_lh

theorem load_address_lw (s : State) (i : Inputs)
    (alu : DecodedAluAligned s) (agree : RegisterAgreement s) (zero : ReferenceZero s)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v2095 s i := by
  have value := (decoded_alu_reference_operands s alu agree).trans
    (decoded_execution_lw _ _ _ _ known)
  rw [← reference_lw_operand1 s i zero commit known,
    ← reference_lw_immediate s i commit known] at value
  exact value.trans (reference_load_address s i).symm
#print axioms load_address_lw

theorem load_address_lbu (s : State) (i : Inputs)
    (alu : DecodedAluAligned s) (agree : RegisterAgreement s) (zero : ReferenceZero s)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v2095 s i := by
  have value := (decoded_alu_reference_operands s alu agree).trans
    (decoded_execution_lbu _ _ _ _ known)
  rw [← reference_lbu_operand1 s i zero commit known,
    ← reference_lbu_immediate s i commit known] at value
  exact value.trans (reference_load_address s i).symm
#print axioms load_address_lbu

theorem load_address_lhu (s : State) (i : Inputs)
    (alu : DecodedAluAligned s) (agree : RegisterAgreement s) (zero : ReferenceZero s)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v2095 s i := by
  have value := (decoded_alu_reference_operands s alu agree).trans
    (decoded_execution_lhu _ _ _ _ known)
  rw [← reference_lhu_operand1 s i zero commit known,
    ← reference_lhu_immediate s i commit known] at value
  exact value.trans (reference_load_address s i).symm
#print axioms load_address_lhu

theorem load_address_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (instruction : LoadInstruction (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) :
    (run initial inputs t).g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu =
      v2095 (run initial inputs t) (inputs t) := by
  have alu := decoded_alu_alignment_reachable initial inputs cycles reset env t ht
  have zero := reference_zero_reachable initial inputs cycles reset t ht
  cases instruction with
  | op_lb known => exact load_address_lb _ _ alu agree zero commit known
  | op_lh known => exact load_address_lh _ _ alu agree zero commit known
  | op_lw known => exact load_address_lw _ _ alu agree zero commit known
  | op_lbu known => exact load_address_lbu _ _ alu agree zero commit known
  | op_lhu known => exact load_address_lhu _ _ alu agree zero commit known
#print axioms load_address_reachable
#print axioms reference_load_response
end RiscvMiniProofs
