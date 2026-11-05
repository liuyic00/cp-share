import Proofs.StoreDataCone
import Proofs.ControlAlignment
import Proofs.PcBridge
namespace RiscvMiniProofs
open nCoreSoc

structure StoreEncodingValues (s : State) : Prop where
  mask : s.g4.r141_ndut_5Fdpath_5Fmem_5Fwmask =
    storeMask (decode_store s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst)
      s.g4.r154_ndut_5Fdpath_5Freq_5Faddr
      (dutRead s (BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst))
  data : s.g4.r142_ndut_5Fdpath_5Fmem_5Fwdata =
    storeData (decode_store s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst)
      s.g4.r154_ndut_5Fdpath_5Freq_5Faddr
      (dutRead s (BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst))

def StoreEncoding (s : State) : Prop :=
  s.g4.r144_ndut_5Fdpath_5FinstCommit_5Fpredit_5FREG_5F1 = 0 → StoreEncodingValues s

theorem store_encoding_reset (s : State) (i : Inputs) (reset : i.nreset = 1) :
    StoreEncoding (step s i) := by
  intro valid
  change v8567 s i = 0 at valid
  simp [v8567, v1, v0, reset, v512] at valid

theorem store_encoding_step (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (hazard : HazardAligned s) :
    StoreEncodingValues (step s i) := by
  have trap := environment_no_trap s i reset env
  have stall := no_stall_after_reset s i reset
  have transfer := execute_transfer_step s i reset env
  have source := forwarding_aligned_port2 s i hazard reset trap
  have request : (step s i).g4.r154_ndut_5Fdpath_5Freq_5Faddr = v8492 s i := by
    change v8602 s i = _
    simp [v8602, v8601, v1, v0, reset, stall]
  have kind : v8522 s i = decode_store s.g3.r123_ndut_5Fdpath_5Ffe_5Freg_5Finst := by
    simp [v8522, stall, decode_store_eq]
  constructor
  · change v8542 s i = _
    rw [transfer.instruction, request]
    simp only [v8542, v1, v0, reset, BitVec.reduceEq, ↓reduceIte,
      store_mask_cone, kind, source]
    rfl
  · change v8561 s i = _
    rw [transfer.instruction, request]
    simp only [v8561, v1, v0, reset, BitVec.reduceEq, ↓reduceIte,
      store_data_cone, kind, source]
    rfl

theorem store_encoding_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) : StoreEncoding (run initial inputs t) := by
  cases t with
  | zero => have := reset.1; omega
  | succ n =>
    by_cases prev : cycles ≤ n
    · intro _
      exact store_encoding_step _ _ (reset.2.2 n prev) (env n)
        (hazard_alignment_reachable initial inputs cycles reset env n prev)
    · exact store_encoding_reset _ _ (reset.2.1 n (by omega))

#print axioms store_encoding_reachable
end RiscvMiniProofs
