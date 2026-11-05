import Proofs.PcCheckAlignment
import Proofs.NonbranchCheckDecode
namespace RiscvMiniProofs
open nCoreSoc

-- Architectural successor expressed solely using saved DUT state.
def writebackNextPc (s : State) : BitVec 32 :=
  if s.g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = 1 then
    (BitVec.extractLsb' 1 31 s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu) ++ (0#1)
  else s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc + 4

theorem clear_even_target (x : BitVec 32) (even : BitVec.extractLsb' 0 1 x = 0) :
    (BitVec.extractLsb' 1 31 x) ++ (0#1) = x := by
  have bit := congrArg (fun b : BitVec 1 => b.getLsbD 0) even
  have low : x[0] = false := by simpa using bit
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  by_cases h : j = 0
  · subst j
    simp [BitVec.getElem_append (n := 31) (m := 1), low]
  · simp [BitVec.getElem_append (n := 31) (m := 1), BitVec.getElem_extractLsb',
      show ¬j < 1 by omega, show j-1 < 31 by omega, show 1+(j-1)=j by omega, hj]

#print axioms clear_even_target
end RiscvMiniProofs
