import Proofs.RegisterBridge
namespace RiscvMiniProofs
open nCoreSoc

theorem register_tasks_idle (s : State) (i : Inputs) (idle : v964 s i = 0) :
    RegisterTasks s i := by
  have idleWire : v962 s i = 0 := idle
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change decide (v9293 s i ≠ 1 ∨ v9291 s i = 1) = true
    simp [v9293, idleWire]
  · change decide (v9303 s i ≠ 1 ∨ v9301 s i = 1) = true
    simp [v9303, idleWire]
  · change decide (v9313 s i ≠ 1 ∨ v9311 s i = 1) = true
    simp [v9313, idleWire]
  · change decide (v9323 s i ≠ 1 ∨ v9321 s i = 1) = true
    simp [v9323, idleWire]
  · change decide (v9333 s i ≠ 1 ∨ v9331 s i = 1) = true
    simp [v9333, idleWire]
  · change decide (v9343 s i ≠ 1 ∨ v9341 s i = 1) = true
    simp [v9343, idleWire]
  · change decide (v9353 s i ≠ 1 ∨ v9351 s i = 1) = true
    simp [v9353, idleWire]
  · change decide (v9363 s i ≠ 1 ∨ v9361 s i = 1) = true
    simp [v9363, idleWire]
  · change decide (v9373 s i ≠ 1 ∨ v9371 s i = 1) = true
    simp [v9373, idleWire]
  · change decide (v9383 s i ≠ 1 ∨ v9381 s i = 1) = true
    simp [v9383, idleWire]
  · change decide (v9393 s i ≠ 1 ∨ v9391 s i = 1) = true
    simp [v9393, idleWire]
  · change decide (v9403 s i ≠ 1 ∨ v9401 s i = 1) = true
    simp [v9403, idleWire]
  · change decide (v9413 s i ≠ 1 ∨ v9411 s i = 1) = true
    simp [v9413, idleWire]
  · change decide (v9423 s i ≠ 1 ∨ v9421 s i = 1) = true
    simp [v9423, idleWire]
  · change decide (v9433 s i ≠ 1 ∨ v9431 s i = 1) = true
    simp [v9433, idleWire]
  · change decide (v9442 s i ≠ 1 ∨ v9440 s i = 1) = true
    simp [v9442, idleWire]
  · change decide (v9451 s i ≠ 1 ∨ v9449 s i = 1) = true
    simp [v9451, idleWire]
  · change decide (v9460 s i ≠ 1 ∨ v9458 s i = 1) = true
    simp [v9460, idleWire]
  · change decide (v9469 s i ≠ 1 ∨ v9467 s i = 1) = true
    simp [v9469, idleWire]
  · change decide (v9478 s i ≠ 1 ∨ v9476 s i = 1) = true
    simp [v9478, idleWire]
  · change decide (v9487 s i ≠ 1 ∨ v9485 s i = 1) = true
    simp [v9487, idleWire]
  · change decide (v9496 s i ≠ 1 ∨ v9494 s i = 1) = true
    simp [v9496, idleWire]
  · change decide (v9505 s i ≠ 1 ∨ v9503 s i = 1) = true
    simp [v9505, idleWire]
  · change decide (v9514 s i ≠ 1 ∨ v9512 s i = 1) = true
    simp [v9514, idleWire]
  · change decide (v9523 s i ≠ 1 ∨ v9521 s i = 1) = true
    simp [v9523, idleWire]
  · change decide (v9532 s i ≠ 1 ∨ v9530 s i = 1) = true
    simp [v9532, idleWire]
  · change decide (v9541 s i ≠ 1 ∨ v9539 s i = 1) = true
    simp [v9541, idleWire]
  · change decide (v9550 s i ≠ 1 ∨ v9548 s i = 1) = true
    simp [v9550, idleWire]
  · change decide (v9559 s i ≠ 1 ∨ v9557 s i = 1) = true
    simp [v9559, idleWire]
  · change decide (v9568 s i ≠ 1 ∨ v9566 s i = 1) = true
    simp [v9568, idleWire]
  · change decide (v9577 s i ≠ 1 ∨ v9575 s i = 1) = true
    simp [v9577, idleWire]

theorem register_tasks_at_index (s : State) (i : Inputs) (registers : RegisterTasks s i)
    (task : Fin 45) (lo : 9 ≤ task.val) (hi : task.val ≤ 39) : TaskHolds task s i := by
  rcases registers with ⟨h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39⟩
  rcases task with ⟨n, bound⟩
  have cases : n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨ n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨ n = 24 ∨ n = 25 ∨ n = 26 ∨ n = 27 ∨ n = 28 ∨ n = 29 ∨ n = 30 ∨ n = 31 ∨ n = 32 ∨ n = 33 ∨ n = 34 ∨ n = 35 ∨ n = 36 ∨ n = 37 ∨ n = 38 ∨ n = 39 := by change 9 ≤ n at lo; change n ≤ 39 at hi; omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h9
  · exact h10
  · exact h11
  · exact h12
  · exact h13
  · exact h14
  · exact h15
  · exact h16
  · exact h17
  · exact h18
  · exact h19
  · exact h20
  · exact h21
  · exact h22
  · exact h23
  · exact h24
  · exact h25
  · exact h26
  · exact h27
  · exact h28
  · exact h29
  · exact h30
  · exact h31
  · exact h32
  · exact h33
  · exact h34
  · exact h35
  · exact h36
  · exact h37
  · exact h38
  · exact h39

#print axioms register_tasks_idle
#print axioms register_tasks_at_index
end RiscvMiniProofs
