import Proofs.UpperExecution
import Proofs.ReferenceExecution
import Proofs.PcRelation
namespace RiscvMiniProofs
open nCoreSoc

theorem reference_auipc_value (s : State) (i : Inputs) :
    v2309 s i = v2222 s i + v2092 s i := by
  change refExec_v2303 (v2222 s i) (v2092 s i) = _
  exact reference_execution_add _ _

#print axioms reference_auipc_value
end RiscvMiniProofs
