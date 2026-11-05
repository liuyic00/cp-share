import Proofs.Contract
namespace RiscvMiniProofs
open nCoreSoc

-- A relation needed when an instruction commits, not an environment assumption.
-- It is false in reset bubbles; PcBridge guards it by writeback validity.
-- Reachability of that guarded relation remains an outstanding obligation.
def WritebackPcAgreement (s : State) : Prop :=
  s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
    s.g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc

end RiscvMiniProofs
