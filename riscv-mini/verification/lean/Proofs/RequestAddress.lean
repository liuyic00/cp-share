import Proofs.LoadExecution
import Proofs.StoreExecution
namespace RiscvMiniProofs
open nCoreSoc

theorem request_address_step (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (op : v7840 s i = 0) :
    (step s i).g4.r154_ndut_5Fdpath_5Freq_5Faddr =
      (step s i).g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu := by
  have stall := no_stall_after_reset s i reset
  rw [(execute_transfer_step s i reset env).alu, ← circuit_alu_eq]
  change v8602 s i = v8164 s i
  simp [v8602, v8601, v8492, v1, v0, reset, stall,
    v8164, v8163, v7843, v7841, v7842, v725, v7793, op]

theorem request_address_reset (s : State) (i : Inputs) (reset : i.nreset = 1) :
    (step s i).g4.r154_ndut_5Fdpath_5Freq_5Faddr =
      (step s i).g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu := by
  change v8602 s i = v8167 s i
  simp [v8602, v8167, v1, v0, reset, v8600, v3]

theorem request_address_reachable_of_op (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (op : exec_v7840 (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 0 0 0 = 0) :
    (run initial inputs t).g4.r154_ndut_5Fdpath_5Freq_5Faddr =
      (run initial inputs t).g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu := by
  cases t with
  | zero => have := reset.1; omega
  | succ n =>
    by_cases prev : cycles ≤ n
    · have transfer := execute_transfer_reachable initial inputs cycles reset env n prev
      rw [transfer.instruction] at op
      exact request_address_step _ _ (reset.2.2 n prev) (env n) op
    · exact request_address_reset _ _ (reset.2.1 n (by omega))

#print axioms request_address_reachable_of_op
end RiscvMiniProofs
