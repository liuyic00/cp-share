import Proofs.PcBridge
namespace RiscvMiniProofs
open nCoreSoc

private theorem unsupported_legacy_return (s : State) (i : Inputs)
    (instruction : v9046 s i = 268435571#32) (valid : v9040 s i = 1#1) :
    v9797 s i = 0 := by
  simp only [v4, v9625, v9626, v9627, v9628, v9629, v9630, v9631, v9632, v9633, v9634, v9635, v9636, v9637, v9638, v9639, v9640, v9641, v9642, v9643, v9644, v9645, v9646, v9647, v9648, v9649, v9650, v9651, v9652, v9653, v9654, v9655, v9656, v9657, v9658, v9659, v9660, v9661, v9662, v9663, v9664, v9665, v9666, v9667, v9668, v9669, v9670, v9671, v9672, v9673, v9674, v9675, v9676, v9677, v9678, v9679, v9680, v9681, v9682, v9683, v9684, v9685, v9686, v9687, v9688, v9689, v9690, v9691, v9692, v9693, v9694, v9695, v9696, v9697, v9698, v9699, v9700, v9701, v9702, v9703, v9704, v9705, v9706, v9707, v9708, v9709, v9710, v9711, v9712, v9713, v9714, v9715, v9716, v9717, v9718, v9719, v9720, v9721, v9722, v9723, v9724, v9725, v9726, v9727, v9728, v9729, v9730, v9731, v9732, v9733, v9734, v9735, v9736, v9737, v9738, v9739, v9740, v9741, v9742, v9743, v9744, v9745, v9746, v9747, v9748, v9749, v9750, v9751, v9752, v9753, v9754, v9755, v9756, v9757, v9758, v9759, v9760, v9761, v9762, v9763, v9764, v9765, v9766, v9767, v9768, v9769, v9770, v9771, v9772, v9773, v9774, v9775, v9776, v9777, v9778, v9779, v978, v9780, v9781, v9782, v9783, v9784, v9785, v9786, v9787, v9788, v9789, v9790, v9791, v9792, v9793, v9794, v9795, v9796, v9797, instruction, valid]
  decide

theorem environment_excludes_legacy_return (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (bubbles : BubbleAlignment s) :
    s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 268435571 := by
  intro instruction
  have live : s.g4.r144_ndut_5Fdpath_5FinstCommit_5Fpredit_5FREG_5F1 = 0 := by
    rcases BitVec.eq_zero_or_eq_one s.g4.r144_ndut_5Fdpath_5FinstCommit_5Fpredit_5FREG_5F1 with hz | ho
    · exact hz
    · have nop := bubbles.writeback ho
      rw [instruction] at nop
      contradiction
  have commit := (commit_iff_valid_writeback s i reset).mpr live
  have valid : v9040 s i = 1#1 := commit
  have checked : v9046 s i = 268435571#32 := by
    simp [v9046, v9045, v9044, v9043, v512, valid, instruction]
  have unsupported := unsupported_legacy_return s i checked valid
  simp [assumes, eval, assumptionChecks, assumptionChecks0,
    v9801, v9800, v9799, v4, reset, unsupported] at env

theorem fetch_excludes_legacy_return (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) :
    (run initial inputs t).g3.r123_ndut_5Fdpath_5Ffe_5Freg_5Finst ≠ 268435571 := by
  have next := environment_excludes_legacy_return (run initial inputs (t+1)) (inputs (t+1))
    (reset.2.2 (t+1) (by omega)) (env (t+1))
    (bubble_alignment_reachable initial inputs cycles reset env (t+1) (by omega))
  have transfer := (execute_transfer_reachable initial inputs cycles reset env t ht).instruction
  rw [transfer] at next
  exact next

#print axioms environment_excludes_legacy_return
#print axioms fetch_excludes_legacy_return
theorem no_legacy_return_select (s : State) (i : Inputs)
    (known : s.g3.r123_ndut_5Fdpath_5Ffe_5Freg_5Finst ≠ 268435571) : v8487 s i = 0 := by
  have h8424 : v8424 s i ≠ 3#2 := by
    have no : s.g3.r123_ndut_5Fdpath_5Ffe_5Freg_5Finst ≠ 268435571#32 := known
    simp [v8424, v7470, v7469, v7300, v7299, v32, Ne.symm no]
  have h8425 : v8425 s i ≠ 3#2 := by
    simp only [v8425, v32]
    split <;> first | decide | exact h8424
  have h8426 : v8426 s i ≠ 3#2 := by
    simp only [v8426, v32]
    split <;> first | decide | exact h8425
  have h8427 : v8427 s i ≠ 3#2 := by
    simp only [v8427, v38]
    split <;> first | decide | exact h8426
  have h8428 : v8428 s i ≠ 3#2 := by
    simp only [v8428, v38]
    split <;> first | decide | exact h8427
  have h8429 : v8429 s i ≠ 3#2 := by
    simp only [v8429, v38]
    split <;> first | decide | exact h8428
  have h8430 : v8430 s i ≠ 3#2 := by
    simp only [v8430, v38]
    split <;> first | decide | exact h8429
  have h8431 : v8431 s i ≠ 3#2 := by
    simp only [v8431, v38]
    split <;> first | decide | exact h8430
  have h8432 : v8432 s i ≠ 3#2 := by
    simp only [v8432, v38]
    split <;> first | decide | exact h8431
  have h8433 : v8433 s i ≠ 3#2 := by
    simp only [v8433, v38]
    split <;> first | decide | exact h8432
  have h8434 : v8434 s i ≠ 3#2 := by
    simp only [v8434, v32]
    split <;> first | decide | exact h8433
  have h8435 : v8435 s i ≠ 3#2 := by
    simp only [v8435, v32]
    split <;> first | decide | exact h8434
  have h8436 : v8436 s i ≠ 3#2 := by
    simp only [v8436, v32]
    split <;> first | decide | exact h8435
  have h8437 : v8437 s i ≠ 3#2 := by
    simp only [v8437, v32]
    split <;> first | decide | exact h8436
  have h8438 : v8438 s i ≠ 3#2 := by
    simp only [v8438, v32]
    split <;> first | decide | exact h8437
  have h8439 : v8439 s i ≠ 3#2 := by
    simp only [v8439, v32]
    split <;> first | decide | exact h8438
  have h8440 : v8440 s i ≠ 3#2 := by
    simp only [v8440, v32]
    split <;> first | decide | exact h8439
  have h8441 : v8441 s i ≠ 3#2 := by
    simp only [v8441, v32]
    split <;> first | decide | exact h8440
  have h8442 : v8442 s i ≠ 3#2 := by
    simp only [v8442, v32]
    split <;> first | decide | exact h8441
  have h8443 : v8443 s i ≠ 3#2 := by
    simp only [v8443, v32]
    split <;> first | decide | exact h8442
  have h8444 : v8444 s i ≠ 3#2 := by
    simp only [v8444, v32]
    split <;> first | decide | exact h8443
  have h8445 : v8445 s i ≠ 3#2 := by
    simp only [v8445, v32]
    split <;> first | decide | exact h8444
  have h8446 : v8446 s i ≠ 3#2 := by
    simp only [v8446, v32]
    split <;> first | decide | exact h8445
  have h8447 : v8447 s i ≠ 3#2 := by
    simp only [v8447, v32]
    split <;> first | decide | exact h8446
  have h8448 : v8448 s i ≠ 3#2 := by
    simp only [v8448, v32]
    split <;> first | decide | exact h8447
  have h8449 : v8449 s i ≠ 3#2 := by
    simp only [v8449, v32]
    split <;> first | decide | exact h8448
  have h8450 : v8450 s i ≠ 3#2 := by
    simp only [v8450, v32]
    split <;> first | decide | exact h8449
  have h8451 : v8451 s i ≠ 3#2 := by
    simp only [v8451, v32]
    split <;> first | decide | exact h8450
  have h8452 : v8452 s i ≠ 3#2 := by
    simp only [v8452, v32]
    split <;> first | decide | exact h8451
  have h8453 : v8453 s i ≠ 3#2 := by
    simp only [v8453, v32]
    split <;> first | decide | exact h8452
  have h8454 : v8454 s i ≠ 3#2 := by
    simp only [v8454, v32]
    split <;> first | decide | exact h8453
  have h8455 : v8455 s i ≠ 3#2 := by
    simp only [v8455, v32]
    split <;> first | decide | exact h8454
  have h8456 : v8456 s i ≠ 3#2 := by
    simp only [v8456, v32]
    split <;> first | decide | exact h8455
  have h8457 : v8457 s i ≠ 3#2 := by
    simp only [v8457, v38]
    split <;> first | decide | exact h8456
  have h8458 : v8458 s i ≠ 3#2 := by
    simp only [v8458, v38]
    split <;> first | decide | exact h8457
  have h8459 : v8459 s i ≠ 3#2 := by
    simp only [v8459, v38]
    split <;> first | decide | exact h8458
  have h8460 : v8460 s i ≠ 3#2 := by
    simp only [v8460, v38]
    split <;> first | decide | exact h8459
  have h8461 : v8461 s i ≠ 3#2 := by
    simp only [v8461, v38]
    split <;> first | decide | exact h8460
  have h8462 : v8462 s i ≠ 3#2 := by
    simp only [v8462, v32]
    split <;> first | decide | exact h8461
  have h8463 : v8463 s i ≠ 3#2 := by
    simp only [v8463, v32]
    split <;> first | decide | exact h8462
  have h8464 : v8464 s i ≠ 3#2 := by
    simp only [v8464, v32]
    split <;> first | decide | exact h8463
  have h8465 : v8465 s i ≠ 3#2 := by
    simp only [v8465, v32]
    split <;> first | decide | exact h8464
  have h8466 : v8466 s i ≠ 3#2 := by
    simp only [v8466, v32]
    split <;> first | decide | exact h8465
  have h8467 : v8467 s i ≠ 3#2 := by
    simp only [v8467, v32]
    split <;> first | decide | exact h8466
  have h8468 : v8468 s i ≠ 3#2 := by
    simp only [v8468, v42]
    split <;> first | decide | exact h8467
  have h8469 : v8469 s i ≠ 3#2 := by
    simp only [v8469, v42]
    split <;> first | decide | exact h8468
  have h8470 : v8470 s i ≠ 3#2 := by
    simp only [v8470, v32]
    split <;> first | decide | exact h8469
  have h8471 : v8471 s i ≠ 3#2 := by
    simp only [v8471, v32]
    split <;> first | decide | exact h8470
  have ne : v8473 s i ≠ 3#2 := h8471
  simpa only [v8487, v155] using (if_neg ne)
#print axioms no_legacy_return_select
end RiscvMiniProofs
