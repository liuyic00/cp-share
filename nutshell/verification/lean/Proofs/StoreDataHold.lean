import Proofs.StoreDataCapture
namespace NutShellProofs
open nNutCore

theorem store_formatted_data_hold (s : State) (i next : Inputs)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (nextOuter : (step s i).g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (hold : v24283 s i ≠ 1) : v14539 (step s i) next = v14539 s i := by
  have op : v11569 (step s i) next = v11569 s i := by
    simp only [v11569, v11568, v11519, v2687, outer, nextOuter, ↓reduceIte, v11526]
    change v24928 s i = v28 s i
    simp only [v24928, hold, ↓reduceIte, v28]
  have data : v14512 (step s i) next = v14512 s i := by
    simp only [v14512, v14511, v11519, v2687, outer, nextOuter, ↓reduceIte, v12471]
    change v25325 s i = v12149 s i
    simp only [v25325, hold, ↓reduceIte, v12149]
  simp only [v14539, v14538, v14537, v14536, v14532, v14526, v14518, v14497, v14496, v14454, v14516, v14515, v14514, v14513, v14517, v14525, v14520, v14519, v14523, v14522, v14521, v14524, v14531, v14527, v9721, v14529, v14528, v14530, v14535, v14533, v2750, v14534, op, data]

def StoreDataLatched (s : State) (i : Inputs) : Prop :=
  s.g44.r1436_nbackend_5Fexu_5Fmem_5Frvfi_5Freg_5Fwdata = v14539 s i

theorem store_data_latched_step (s : State) (i next : Inputs)
    (reset : i.g0.nreset = 0) (unit : v3 s i = 1)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (nextOuter : (step s i).g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (hold : v24283 s i ≠ 1)
    (source : v12570 s i = 1 ∨ StoreDataLatched s i) :
    StoreDataLatched (step s i) next := by
  unfold StoreDataLatched
  rw [store_data_latch_step s i reset unit,
    store_formatted_data_hold s i next outer nextOuter hold]
  rcases source with request | old
  · simp [request]
  · change s.g44.r1436_nbackend_5Fexu_5Fmem_5Frvfi_5Freg_5Fwdata = v14539 s i at old
    simp [old]
#print axioms store_formatted_data_hold
#print axioms store_data_latched_step
end NutShellProofs
