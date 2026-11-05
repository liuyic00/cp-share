import Proofs.MemoryMaskCapture
namespace NutShellProofs
open nNutCore

theorem memory_shifted_mask_hold (s : State) (i next : Inputs)
    (idle : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (nextIdle : (step s i).g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (hold : v24283 s i ≠ 1) : v14480 (step s i) next = v14480 s i := by
  have address := lsu_address_hold_without_capture s i next idle nextIdle hold
  have op : v11569 (step s i) next = v11569 s i := by
    simp only [v11569, v11568, v11519, v2687, idle, nextIdle, ↓reduceIte, v11526]
    change v24928 s i = v28 s i
    simp only [v24928, hold, ↓reduceIte, v28]
  simp only [v14480, v14479, v14478, v14477, v14476, v14473, v14452, v14472, v14467, v8317, v14466, v14462, v4079, v14461, v14456, v24, v14455, v14453, v14454, v14460, v14458, v14457, v2750, v14459, v14465, v14463, v9721, v15, v14464, v14471, v14468, v14469, v14470, v14475, v10038, v14474, address, op]

/-- The latch agrees with the current combinational read/write mask. -/
def MemoryMasksLatched (s : State) (i : Inputs) : Prop :=
  s.g44.r1433_nbackend_5Fexu_5Fmem_5Frvfi_5Freg_5Frmask = v14482 s i ∧
  s.g44.r1434_nbackend_5Fexu_5Fmem_5Frvfi_5Freg_5Fwmask = v14489 s i

theorem memory_masks_latched_step (s : State) (i next : Inputs)
    (reset : i.g0.nreset = 0) (unit : v3 s i = 1)
    (readStable : v14482 (step s i) next = v14482 s i)
    (writeStable : v14489 (step s i) next = v14489 s i)
    (source : v12570 s i = 1 ∨ MemoryMasksLatched s i) :
    MemoryMasksLatched (step s i) next := by
  unfold MemoryMasksLatched
  rw [memory_read_mask_latch_step s i reset unit,
    memory_write_mask_latch_step s i reset unit, readStable, writeStable]
  rcases source with request | old
  · simp [request]
  · rcases old with ⟨read, write⟩
    simp [read, write]
#print axioms memory_shifted_mask_hold
#print axioms memory_masks_latched_step
theorem memory_mask_routing_hold (s : State) (i next : Inputs)
    (idle : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (nextIdle : (step s i).g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (hold : v24283 s i ≠ 1)
    (enabled : v11546 (step s i) next = v11546 s i) :
    v14482 (step s i) next = v14482 s i ∧
    v14489 (step s i) next = v14489 s i := by
  have mask := memory_shifted_mask_hold s i next idle nextIdle hold
  have op : v11569 (step s i) next = v11569 s i := by
    simp only [v11569, v11568, v11519, v2687, idle, nextIdle, ↓reduceIte, v11526]
    change v24928 s i = v28 s i
    simp only [v24928, hold, ↓reduceIte, v28]
  simp only [v14482, v14489, v14451, v14487, v14449, v14448, v12314,
    v12313, v11571, v11570, v14450, v14486, v14481, v14488, v2687,
    mask, op, enabled, and_self]
#print axioms memory_mask_routing_hold
end NutShellProofs
