import Proofs.DecodeCases
namespace RiscvMiniProofs
open nCoreSoc

structure MemoryControl (s : State) : Prop where
  load : s.g4.r130_ndut_5Fdpath_5Fld_5Ftype = decode_load s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst
  width : s.g4.r158_ndut_5Fdpath_5Fmem_5Fwrite_5FmemWidth_5FREG = decode_store_width s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst
  valid : s.g4.r157_ndut_5Fdpath_5Fmem_5Fwrite_5Fvalid_5FREG = decode_store_valid s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst

theorem memory_control_reset (s : State) (i : Inputs) (reset : i.nreset = 1) :
    MemoryControl (step s i) := by
  have load := addi_load (19#32) (by decide)
  have store := addi_store (19#32) (by decide)
  have keep : v7774 s i = 1 := by
    simp only [v7774, v7772, v1, v0, reset]
    exact BitVec.allOnes_or
  constructor
  · change v8215 s i = decode_load (v7780 s i)
    simpa [v8215, keep, v8196, v1, v0, reset, v7780, v427] using load.symm
  · change v8622 s i = decode_store_width (v7780 s i)
    simp [v8622, v1, v0, reset, v8621, v7780, v427, decode_store_width, store]
  · change v8620 s i = decode_store_valid (v7780 s i)
    simp [v8620, v1, v0, reset, v4, v7780, v427, decode_store_valid, decode_store_width, store]

theorem memory_control_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) : MemoryControl (run initial inputs t) := by
  cases t with
  | zero => have := reset.1; omega
  | succ n =>
    by_cases prev : cycles ≤ n
    · have control := control_values_step (run initial inputs n) (inputs n)
        (reset.2.2 n prev) (environment_no_trap _ _ (reset.2.2 n prev) (env n))
      exact ⟨control.load, control.store_width, control.store_valid⟩
    · exact memory_control_reset _ _ (reset.2.1 n (by omega))

#print axioms memory_control_reachable
end RiscvMiniProofs
