import Proofs.NonMemoryEvents
namespace NutShellProofs
open nNutCore
set_option maxRecDepth 4096
theorem reference_nonmemory_events_zero (s : State) (i : Inputs)
    (nonmemory : ∀ op : MemoryOp, v14575 s i &&& 28799 ≠ op.encoding.setWidth 32) :
    v31135 s i = 0 ∧ v31224 s i = 0 := by
  have h_v14893 : v14893 s i = 0 := by
    have miss := nonmemory .lb
    simp only [MemoryOp.encoding] at miss
    simp [v14893, v14890, v14892, v14891]
    exact Ne.symm miss
  have h_v14885 : v14885 s i = 0 := by
    have miss := nonmemory .lh
    simp only [MemoryOp.encoding] at miss
    simp [v14885, v14882, v14884, v14883]
    exact Ne.symm miss
  have h_v14877 : v14877 s i = 0 := by
    have miss := nonmemory .lw
    simp only [MemoryOp.encoding] at miss
    simp [v14877, v14874, v14876, v14875]
    exact Ne.symm miss
  have h_v14710 : v14710 s i = 0 := by
    have miss := nonmemory .ld
    simp only [MemoryOp.encoding] at miss
    simp [v14710, v14707, v14709, v14708]
    exact Ne.symm miss
  have h_v14869 : v14869 s i = 0 := by
    have miss := nonmemory .lbu
    simp only [MemoryOp.encoding] at miss
    simp [v14869, v14866, v14868, v14867]
    exact Ne.symm miss
  have h_v14861 : v14861 s i = 0 := by
    have miss := nonmemory .lhu
    simp only [MemoryOp.encoding] at miss
    simp [v14861, v14858, v14860, v14859]
    exact Ne.symm miss
  have h_v14718 : v14718 s i = 0 := by
    have miss := nonmemory .lwu
    simp only [MemoryOp.encoding] at miss
    simp [v14718, v14715, v14717, v14716]
    exact Ne.symm miss
  have h_v15186 : v15186 s i = 0 := by
    have miss := nonmemory .sb
    simp only [MemoryOp.encoding] at miss
    simp [v15186, v15183, v15185, v15184]
    exact Ne.symm miss
  have h_v15180 : v15180 s i = 0 := by
    have miss := nonmemory .sh
    simp only [MemoryOp.encoding] at miss
    simp [v15180, v15177, v15179, v15178]
    exact Ne.symm miss
  have h_v15174 : v15174 s i = 0 := by
    have miss := nonmemory .sw
    simp only [MemoryOp.encoding] at miss
    simp [v15174, v15171, v15173, v15172]
    exact Ne.symm miss
  have h_v15160 : v15160 s i = 0 := by
    have miss := nonmemory .sd
    simp only [MemoryOp.encoding] at miss
    simp [v15160, v15157, v15159, v15158]
    exact Ne.symm miss
  constructor
  · simp [v31135, v31134, v31133, v31132, v31130, v31128, v31126, v31125, v31123, v24, h_v14893, h_v14885, h_v14877, h_v14710, h_v14869, h_v14861, h_v14718, h_v15186, h_v15180, h_v15174, h_v15160]
  · simp [v31224, v31223, v31222, v31221, v31219, v31217, v24, h_v14893, h_v14885, h_v14877, h_v14710, h_v14869, h_v14861, h_v14718, h_v15186, h_v15180, h_v15174, h_v15160]
#print axioms reference_nonmemory_events_zero
end NutShellProofs
