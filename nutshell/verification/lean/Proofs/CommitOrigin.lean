import Proofs.ExecuteOrigin

namespace NutShellProofs
open nNutCore

-- WBU reports zero for a zero source-register index, as in the actual EXU.
def observedSource1 (p : ExecutePayload) : BitVec 64 :=
  if p.field43 = 0 then 0 else p.field52

def observedSource2 (p : ExecutePayload) : BitVec 64 :=
  if p.field44 = 0 then 0 else p.field53

-- Both reported operands refer to the same historical issue, including stalls.
theorem committed_operands_origin (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1) :
    ∃ k, k < t + 1 ∧ v24283 (run initial inputs k) (inputs k) = 1 ∧
      (run initial inputs (t + 2)).g50.r1620_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fdata_5Fsrc1 =
        observedSource1 (executePayload (step (run initial inputs k) (inputs k))) ∧
      (run initial inputs (t + 2)).g50.r1621_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fdata_5Fsrc2 =
        observedSource2 (executePayload (step (run initial inputs k) (inputs k))) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  obtain ⟨k, bound, fire, payload⟩ := execute_payload_origin initial inputs reset t valid
  have c1 := capture_decode_data_src1 _ _ _ commit
  have c2 := capture_decode_data_src2 _ _ _ commit
  have o1 (s : State) (i : Inputs) : v25503 s i = observedSource1 (executePayload s) := by
    simp [v25503, v25502, v25501, v25500, v25465, v25499, v11592,
      observedSource1, executePayload]
  have o2 (s : State) (i : Inputs) : v25509 s i = observedSource2 (executePayload s) := by
    simp [v25509, v25508, v25507, v25506, v25468, v25505, v12149,
      observedSource2, executePayload]
  refine ⟨k, bound, fire, ?_, ?_⟩
  · exact c1.trans ((o1 _ _).trans (congrArg observedSource1 payload))
  · exact c2.trans ((o2 _ _).trans (congrArg observedSource2 payload))

#print axioms committed_operands_origin
end NutShellProofs
