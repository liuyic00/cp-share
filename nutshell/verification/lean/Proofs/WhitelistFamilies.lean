import Proofs.WhitelistCases
import Proofs.ImmediateDecode
import Proofs.ShiftDecode
import Proofs.WordDecode
import Proofs.UpperDecode
import Proofs.RegisterALUDecode
import Proofs.BranchDecode
namespace NutShellProofs
open nNutCore

theorem instruction_mask_low32_lift (instr : BitVec 64) (mask value : BitVec 32)
    (matched : BitVec.extractLsb' 0 32 instr &&& mask = value) :
    instr &&& mask.setWidth 64 = value.setWidth 64 := by
  have extended := congrArg (BitVec.setWidth 64) matched
  rw [← extended]
  apply BitVec.eq_of_getLsbD_eq
  intro bit
  by_cases low : bit < 32
  · simp [BitVec.getLsbD_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', low,
      show bit < 64 by omega]
  · have zero : mask.getLsbD bit = false := BitVec.getLsbD_of_ge mask bit (by omega)
    simp [BitVec.getLsbD_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', low, zero]

inductive MemoryOp where
  | lb | lh | lw | ld | lbu | lhu | lwu | sb | sh | sw | sd
  deriving DecidableEq

def MemoryOp.encoding : MemoryOp → BitVec 64
  | .lb => 3 | .lh => 4099 | .lw => 8195 | .ld => 12291
  | .lbu => 16387 | .lhu => 20483 | .lwu => 24579
  | .sb => 35 | .sh => 4131 | .sw => 8227 | .sd => 12323

def IsMemory (op : MemoryOp) (instr : BitVec 64) : Prop :=
  instr &&& 28799 = op.encoding

inductive JumpOp where
  | jal | jalr
  deriving DecidableEq

def JumpOp.encoding : JumpOp → BitVec 64
  | .jal => 111 | .jalr => 103

def JumpOp.mask : JumpOp → BitVec 64
  | .jal => 127 | .jalr => 28799

def IsJump (op : JumpOp) (instr : BitVec 64) : Prop :=
  instr &&& op.mask = op.encoding

def AllowedInstructionFamily (instr : BitVec 64) : Prop :=
  (∃ op, IsImmediateALU op instr) ∨
  (∃ op, IsShiftImmediate op instr) ∨
  (∃ op, IsWordImmediate op instr) ∨
  (∃ op, IsUpperImmediate op instr) ∨
  (∃ op, IsRegisterALU op instr) ∨
  (∃ op, IsBranch op instr) ∨
  (∃ op, IsJump op instr) ∨
  (∃ op, IsMemory op instr)

#print axioms instruction_mask_low32_lift
end NutShellProofs
