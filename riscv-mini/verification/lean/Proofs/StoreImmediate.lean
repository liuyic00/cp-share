import Proofs.ImmediateFacts
namespace RiscvMiniProofs
def immediateS (instruction : BitVec 32) : BitVec 32 :=
  ((BitVec.extractLsb' 25 7 instruction) ++ (BitVec.extractLsb' 7 5 instruction)).signExtend 32
end RiscvMiniProofs
