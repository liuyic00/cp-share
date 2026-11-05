import Proofs.RegisterALUPipeline
import Proofs.ImmediateArithmetic
namespace NutShellProofs
open nNutCore

def RegisterALUOp.eval (operation : RegisterALUOp) (x y : BitVec 64) : BitVec 64 :=
  match operation with
  | .add => x + y
  | .sub => x - y
  | .slt => if x.toInt < y.toInt then 1 else 0
  | .sltu => if x.toNat < y.toNat then 1 else 0
  | .xor => x ^^^ y
  | .or => x ||| y
  | .and => x &&& y
  | .sll => BitVec.shiftLeft x (BitVec.extractLsb' 0 6 y).toNat
  | .srl => BitVec.ushiftRight x (BitVec.extractLsb' 0 6 y).toNat
  | .sra => BitVec.sshiftRight x (BitVec.extractLsb' 0 6 y).toNat

theorem writeback_register_alu_raw_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : RegisterALUOp)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsRegisterALU operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    v11842 (run initial inputs (t + 2)) (inputs (t + 2)) =
      operation.eval (v12148 (run initial inputs (t + 1)) (inputs (t + 1)))
        (v12150 (run initial inputs (t + 1)) (inputs (t + 1))) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  obtain ⟨op, _, _, _⟩ :=
    (register_alu_decode_run initial inputs reset t).2 valid operation matched unit
  cases operation with
  | add => exact writeback_alu_add _ _ _ commit unit op
  | sub => exact writeback_alu_sub _ _ _ commit unit op
  | slt => exact writeback_alu_slt _ _ _ commit unit op
  | sltu => exact writeback_alu_sltu _ _ _ commit unit op
  | xor => exact writeback_alu_xor _ _ _ commit unit op
  | or => exact writeback_alu_or _ _ _ commit unit op
  | and => exact writeback_alu_and _ _ _ commit unit op
  | sll => exact writeback_alu_sll _ _ _ commit unit op
  | srl => exact writeback_alu_srl _ _ _ commit unit op
  | sra => exact writeback_alu_sra _ _ _ commit unit op

theorem writeback_register_alu_enabled_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : RegisterALUOp)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsRegisterALU operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    v11462 (run initial inputs (t + 2)) (inputs (t + 2)) = 1 := by
  have valid := commit_requires_execute_valid _ _ _ commit
  obtain ⟨_, _, _, enabled⟩ :=
    (register_alu_decode_run initial inputs reset t).2 valid operation matched unit
  exact alu_next_writeback_enabled _ _ _ commit unit enabled


#print axioms writeback_register_alu_raw_run
#print axioms writeback_register_alu_enabled_run
end NutShellProofs
