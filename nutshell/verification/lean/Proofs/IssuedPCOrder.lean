import Proofs.PendingFetchPC
import Proofs.InstructionPCOrder
namespace NutShellProofs
open nNutCore

/-- All issued PCs not yet completed, oldest first, including an in-flight fetch. -/
noncomputable def IssuedPCs (s : State) : List (BitVec 39) :=
  InstructionPCs s ++ PendingFetchPC s

theorem issued_pcs_step (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (flush : v14 s i = 0)
    (bound : QueueOccupancy s ≤ 2)
    (handshake : v11083 s i = v11102 s i)
    (front : v11102 s i = 1 → (FetchPCContents s).head? = some (v10174 s i))
    (notDelivered : FetchNotAlreadyDelivered s) :
    IssuedPCs (step s i) =
      (if v11702 s i = 1 then (IssuedPCs s).tail else IssuedPCs s) ++
      (if v25943 s i = 1 then [s.g33.r1065_nfrontend_5Fifu_5Fpc] else []) := by
  have nonempty : v11702 s i = 1 → InstructionPCs s ≠ [] := by
    intro complete empty
    have first := execute_completion_is_instruction_pc_front s i complete
    simp [empty] at first
  unfold IssuedPCs
  rw [instruction_pcs_step s i reset flush bound handshake front,
    List.append_assoc, pending_fetch_pc_transfer s i reset flush notDelivered,
    ← List.append_assoc]
  by_cases complete : v11702 s i = 1
  · simp only [if_pos complete]
    have tail : (InstructionPCs s).tail ++ PendingFetchPC s =
        (InstructionPCs s ++ PendingFetchPC s).tail := by
      have valid := nonempty complete
      cases h : InstructionPCs s with
      | nil => exact False.elim (valid h)
      | cons a rest => rfl
    rw [tail]
  · simp only [if_neg complete]

theorem issued_pcs_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    IssuedPCs (step s i) = [] := by
  simp [IssuedPCs, instruction_pcs_reset s i reset, pending_fetch_pc_reset s i reset]

theorem issued_pcs_flush (s : State) (i : Inputs) (flush : v14 s i = 1) :
    IssuedPCs (step s i) = [] := by
  simp [IssuedPCs, instruction_pcs_flush s i flush, pending_fetch_pc_flush s i flush]

theorem temporary_pc32_issued_pcs_step (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat)
    (currentReset : (inputs (t + 1)).g0.nreset = 0)
    (noRedirect : v14 (run initial inputs (t + 1)) (inputs (t + 1)) = 0) :
    IssuedPCs (run initial inputs (t + 2)) =
      (if v11702 (run initial inputs (t + 1)) (inputs (t + 1)) = 1
       then (IssuedPCs (run initial inputs (t + 1))).tail
       else IssuedPCs (run initial inputs (t + 1))) ++
      (if v25943 (run initial inputs (t + 1)) (inputs (t + 1)) = 1
       then [(run initial inputs (t + 1)).g33.r1065_nfrontend_5Fifu_5Fpc] else []) := by
  exact issued_pcs_step _ _ currentReset noRedirect
    (queue_occupancy_bound_run initial inputs reset t)
    (temporary_pc32_dequeue_eq_capture_run initial inputs reset environment restriction t
      currentReset noRedirect)
    (temporary_pc32_idu_capture_front initial inputs reset environment restriction t
      currentReset noRedirect)
    (fetch_not_delivered_run initial inputs reset t)

#print axioms temporary_pc32_issued_pcs_step
end NutShellProofs
