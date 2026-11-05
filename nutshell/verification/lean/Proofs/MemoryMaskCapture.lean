import Proofs.MemoryBusyRun
namespace NutShellProofs
open nNutCore

theorem memory_read_mask_latch_step (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (unit : v3 s i = 1) :
    (step s i).g44.r1433_nbackend_5Fexu_5Fmem_5Frvfi_5Freg_5Frmask =
      if v12570 s i = 1 then v14482 s i
      else s.g44.r1433_nbackend_5Fexu_5Fmem_5Frvfi_5Freg_5Frmask := by
  change v14485 s i = _
  simp [v14485, v12103, v11455, reset, v14484, v14443, v14442, unit, v14483]

theorem memory_write_mask_latch_step (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (unit : v3 s i = 1) :
    (step s i).g44.r1434_nbackend_5Fexu_5Fmem_5Frvfi_5Freg_5Fwmask =
      if v12570 s i = 1 then v14489 s i
      else s.g44.r1434_nbackend_5Fexu_5Fmem_5Frvfi_5Freg_5Fwmask := by
  change v14492 s i = _
  simp [v14492, v12103, v11455, reset, v14491, v14443, v14442, unit, v14490]

theorem committed_read_mask_is_latch (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 1) :
    v30865 (step s i) next =
      (step s i).g44.r1433_nbackend_5Fexu_5Fmem_5Frvfi_5Freg_5Frmask := by
  rw [memory_read_mask_latch_step s i (next_commit_controls s i next commit).1 unit]
  change v25586 s i = _
  simp [v25586, commit_requires_capture s i next commit, v25585, v25584,
    v14443, v14442, unit, v25583, v25582, v25580, v25579,
    v14482, v14451, v14450, v14481, v25581]

theorem committed_write_mask_is_latch (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 1) :
    v30869 (step s i) next =
      (step s i).g44.r1434_nbackend_5Fexu_5Fmem_5Frvfi_5Freg_5Fwmask := by
  rw [memory_write_mask_latch_step s i (next_commit_controls s i next commit).1 unit]
  change v25594 s i = _
  simp [v25594, commit_requires_capture s i next commit, v25593, v25592,
    v14443, v14442, unit, v25591, v25590, v25588, v25587,
    v14489, v14487, v14486, v14488, v25589]
#print axioms memory_read_mask_latch_step
#print axioms memory_write_mask_latch_step
#print axioms committed_read_mask_is_latch
#print axioms committed_write_mask_is_latch
def MemoryOp.byteMask : MemoryOp → BitVec 8
  | .lb | .lbu | .sb => 1
  | .lh | .lhu | .sh => 3
  | .lw | .lwu | .sw => 15
  | .ld | .sd => 255

theorem memory_mask_before_shift (s : State) (i : Inputs) (operation : MemoryOp)
    (op : v28 s i = operation.control)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0) :
    v14472 s i = operation.byteMask := by
  cases operation <;>
    simp [v14472, v14467, v14466, v14462, v14461, v14456, v14455,
      v14453, v14454, v14460, v14458, v14457, v14459, v14465,
      v14463, v14464, v14471, v14468, v14469, v14470,
      v11569, v11568, v11519, v2687, outer, v11526, op,
      MemoryOp.control, MemoryOp.byteMask, v24, v2750, v4079,
      v9721, v15, v8317]

#print axioms memory_mask_before_shift
end NutShellProofs
