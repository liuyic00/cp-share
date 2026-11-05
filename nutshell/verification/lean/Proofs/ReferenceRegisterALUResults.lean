import Proofs.RegisterALUReferenceWriteback
namespace NutShellProofs
open nNutCore

private theorem low_sub (x y : BitVec w) (bound : n ≤ w) :
    BitVec.extractLsb' 0 n (x - y) = BitVec.extractLsb' 0 n x - BitVec.extractLsb' 0 n y := by
  simp only [← BitVec.setWidth_eq_extractLsb' bound]
  simp only [BitVec.sub_eq_add_neg, BitVec.setWidth_add _ _ bound, BitVec.setWidth_neg_of_le bound]

theorem reference_register_add_result (s : State) (i : Inputs) :
    v16537 s i = RegisterALUOp.add.eval (v15632 s i) (v15394 s i) := by
  simp only [v16537, v16536, v16534, v16535, low_add _ _ (by decide : 64 ≤ 65),
    BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 64 ≤ 64),
    BitVec.extractLsb'_eq_self, RegisterALUOp.eval]

theorem reference_register_sub_result (s : State) (i : Inputs) :
    v16501 s i = RegisterALUOp.sub.eval (v15632 s i) (v15394 s i) := by
  simp only [v16501, v16500, v16498, v16499, low_sub _ _ (by decide : 64 ≤ 65),
    BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 64 ≤ 64),
    BitVec.extractLsb'_eq_self, RegisterALUOp.eval]

theorem reference_register_xor_result (s : State) (i : Inputs) :
    v16517 s i = RegisterALUOp.xor.eval (v15632 s i) (v15394 s i) := rfl

theorem reference_register_or_result (s : State) (i : Inputs) :
    v16520 s i = RegisterALUOp.or.eval (v15632 s i) (v15394 s i) := rfl

theorem reference_register_and_result (s : State) (i : Inputs) :
    v16523 s i = RegisterALUOp.and.eval (v15632 s i) (v15394 s i) := rfl

theorem reference_register_slt_result (s : State) (i : Inputs) :
    v16531 s i = RegisterALUOp.slt.eval (v15632 s i) (v15394 s i) := by
  simp only [v16531, v16530, v12724, RegisterALUOp.eval]
  split <;> rfl

theorem reference_register_sltu_result (s : State) (i : Inputs) :
    v16527 s i = RegisterALUOp.sltu.eval (v15632 s i) (v15394 s i) := by
  simp only [v16527, v16526, v12724, RegisterALUOp.eval]
  split <;> rfl

theorem reference_register_sll_result (s : State) (i : Inputs) :
    v16280 s i = v15632 s i <<< (BitVec.extractLsb' 0 6 (v15394 s i)).toNat := by
  simp only [v16280, v16279, v16275, v16278, v16277, v16276,
    BitVec.toNat_append, BitVec.toNat_ofNat]
  simp only [Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or]
  have result := low_shiftLeft (v12724 s i ++ v15632 s i)
    (BitVec.extractLsb' 0 6 (v15394 s i)).toNat (by decide : 64 ≤ 127)
  simpa only [BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 64 ≤ 64),
    BitVec.extractLsb'_eq_self] using result

theorem reference_register_srl_result (s : State) (i : Inputs) :
    v16272 s i = v15632 s i >>> (BitVec.extractLsb' 0 6 (v15394 s i)).toNat := by
  simp only [v16272, v16271, v16270, v11483]
  rw [BitVec.toNat_append]
  simp

theorem reference_register_sra_result (s : State) (i : Inputs) :
    v16267 s i = BitVec.sshiftRight (v15632 s i) (BitVec.extractLsb' 0 6 (v15394 s i)).toNat := by
  simp only [v16267, v16266, v16265, v11483]
  rw [BitVec.toNat_append]
  simp


def referenceRegisterALUResult (operation : RegisterALUOp) (s : State) (i : Inputs) : BitVec 64 :=
  match operation with
  | .add => v16537 s i
  | .sub => v16501 s i
  | .slt => v16531 s i
  | .sltu => v16527 s i
  | .xor => v16517 s i
  | .or => v16520 s i
  | .and => v16523 s i
  | .sll => v16280 s i
  | .srl => v16272 s i
  | .sra => v16267 s i

theorem reference_register_alu_result (operation : RegisterALUOp) (s : State) (i : Inputs) :
    referenceRegisterALUResult operation s i = operation.eval (v15632 s i) (v15394 s i) := by
  cases operation with
  | add => exact reference_register_add_result s i
  | sub => exact reference_register_sub_result s i
  | slt => exact reference_register_slt_result s i
  | sltu => exact reference_register_sltu_result s i
  | xor => exact reference_register_xor_result s i
  | or => exact reference_register_or_result s i
  | and => exact reference_register_and_result s i
  | sll => exact reference_register_sll_result s i
  | srl => exact reference_register_srl_result s i
  | sra => exact reference_register_sra_result s i

theorem writeback_register_alu_matches_reference_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : RegisterALUOp)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsRegisterALU operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    v11842 (run initial inputs (t + 2)) (inputs (t + 2)) =
      referenceRegisterALUResult operation (run initial inputs (t + 2)) (inputs (t + 2)) := by
  rw [reference_register_alu_result]
  exact writeback_register_alu_reference_run initial inputs reset t operation commit unit matched aligned

#print axioms reference_register_alu_result
#print axioms writeback_register_alu_matches_reference_run
end NutShellProofs
