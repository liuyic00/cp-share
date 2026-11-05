import Proofs.FetchTransfer
namespace RiscvMiniProofs
open nCoreSoc
set_option linter.unusedSimpArgs false

private theorem control_7470 (s : State) (i : Inputs) :
    v7470 s i = (if v8424 s i = 0 then 0 else 1) := by
  by_cases h : (v7469 s i) = (v7300 s i)
  all_goals simp only [v7470, v8424, v155, v32, h, ↓reduceIte, BitVec.reduceEq]

private theorem control_7471 (s : State) (i : Inputs) :
    v7471 s i = (if v8425 s i = 0 then 0 else 1) := by
  by_cases h : (v7468 s i) = 1
  · simp only [v7471, v8425, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7471, v8425, h, ↓reduceIte] using control_7470 s i

private theorem control_7472 (s : State) (i : Inputs) :
    v7472 s i = (if v8426 s i = 0 then 0 else 1) := by
  by_cases h : (v7466 s i) = 1
  · simp only [v7472, v8426, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7472, v8426, h, ↓reduceIte] using control_7471 s i

private theorem control_7473 (s : State) (i : Inputs) :
    v7473 s i = (if v8427 s i = 0 then 0 else 1) := by
  by_cases h : (v7464 s i) = 1
  · simp only [v7473, v8427, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7473, v8427, h, ↓reduceIte] using control_7472 s i

private theorem control_7474 (s : State) (i : Inputs) :
    v7474 s i = (if v8428 s i = 0 then 0 else 1) := by
  by_cases h : (v7460 s i) = 1
  · simp only [v7474, v8428, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7474, v8428, h, ↓reduceIte] using control_7473 s i

private theorem control_7475 (s : State) (i : Inputs) :
    v7475 s i = (if v8429 s i = 0 then 0 else 1) := by
  by_cases h : (v7456 s i) = 1
  · simp only [v7475, v8429, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7475, v8429, h, ↓reduceIte] using control_7474 s i

private theorem control_7476 (s : State) (i : Inputs) :
    v7476 s i = (if v8430 s i = 0 then 0 else 1) := by
  by_cases h : (v7452 s i) = 1
  · simp only [v7476, v8430, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7476, v8430, h, ↓reduceIte] using control_7475 s i

private theorem control_7477 (s : State) (i : Inputs) :
    v7477 s i = (if v8431 s i = 0 then 0 else 1) := by
  by_cases h : (v7448 s i) = 1
  · simp only [v7477, v8431, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7477, v8431, h, ↓reduceIte] using control_7476 s i

private theorem control_7478 (s : State) (i : Inputs) :
    v7478 s i = (if v8432 s i = 0 then 0 else 1) := by
  by_cases h : (v7444 s i) = 1
  · simp only [v7478, v8432, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7478, v8432, h, ↓reduceIte] using control_7477 s i

private theorem control_7479 (s : State) (i : Inputs) :
    v7479 s i = (if v8433 s i = 0 then 0 else 1) := by
  by_cases h : (v7440 s i) = 1
  · simp only [v7479, v8433, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7479, v8433, h, ↓reduceIte] using control_7478 s i

private theorem control_7480 (s : State) (i : Inputs) :
    v7480 s i = (if v8434 s i = 0 then 0 else 1) := by
  by_cases h : (v7438 s i) = 1
  · simp only [v7480, v8434, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7480, v8434, h, ↓reduceIte] using control_7479 s i

private theorem control_7481 (s : State) (i : Inputs) :
    v7481 s i = (if v8435 s i = 0 then 0 else 1) := by
  by_cases h : (v7434 s i) = 1
  · simp only [v7481, v8435, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7481, v8435, h, ↓reduceIte] using control_7480 s i

private theorem control_7482 (s : State) (i : Inputs) :
    v7482 s i = (if v8436 s i = 0 then 0 else 1) := by
  by_cases h : (v7431 s i) = 1
  · simp only [v7482, v8436, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7482, v8436, h, ↓reduceIte] using control_7481 s i

private theorem control_7483 (s : State) (i : Inputs) :
    v7483 s i = (if v8437 s i = 0 then 0 else 1) := by
  by_cases h : (v7428 s i) = 1
  · simp only [v7483, v8437, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7483, v8437, h, ↓reduceIte] using control_7482 s i

private theorem control_7484 (s : State) (i : Inputs) :
    v7484 s i = (if v8438 s i = 0 then 0 else 1) := by
  by_cases h : (v7425 s i) = 1
  · simp only [v7484, v8438, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7484, v8438, h, ↓reduceIte] using control_7483 s i

private theorem control_7485 (s : State) (i : Inputs) :
    v7485 s i = (if v8439 s i = 0 then 0 else 1) := by
  by_cases h : (v7422 s i) = 1
  · simp only [v7485, v8439, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7485, v8439, h, ↓reduceIte] using control_7484 s i

private theorem control_7486 (s : State) (i : Inputs) :
    v7486 s i = (if v8440 s i = 0 then 0 else 1) := by
  by_cases h : (v7419 s i) = 1
  · simp only [v7486, v8440, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7486, v8440, h, ↓reduceIte] using control_7485 s i

private theorem control_7487 (s : State) (i : Inputs) :
    v7487 s i = (if v8441 s i = 0 then 0 else 1) := by
  by_cases h : (v7416 s i) = 1
  · simp only [v7487, v8441, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7487, v8441, h, ↓reduceIte] using control_7486 s i

private theorem control_7488 (s : State) (i : Inputs) :
    v7488 s i = (if v8442 s i = 0 then 0 else 1) := by
  by_cases h : (v7413 s i) = 1
  · simp only [v7488, v8442, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7488, v8442, h, ↓reduceIte] using control_7487 s i

private theorem control_7489 (s : State) (i : Inputs) :
    v7489 s i = (if v8443 s i = 0 then 0 else 1) := by
  by_cases h : (v7410 s i) = 1
  · simp only [v7489, v8443, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7489, v8443, h, ↓reduceIte] using control_7488 s i

private theorem control_7490 (s : State) (i : Inputs) :
    v7490 s i = (if v8444 s i = 0 then 0 else 1) := by
  by_cases h : (v7407 s i) = 1
  · simp only [v7490, v8444, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7490, v8444, h, ↓reduceIte] using control_7489 s i

private theorem control_7491 (s : State) (i : Inputs) :
    v7491 s i = (if v8445 s i = 0 then 0 else 1) := by
  by_cases h : (v7404 s i) = 1
  · simp only [v7491, v8445, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7491, v8445, h, ↓reduceIte] using control_7490 s i

private theorem control_7492 (s : State) (i : Inputs) :
    v7492 s i = (if v8446 s i = 0 then 0 else 1) := by
  by_cases h : (v7401 s i) = 1
  · simp only [v7492, v8446, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7492, v8446, h, ↓reduceIte] using control_7491 s i

private theorem control_7493 (s : State) (i : Inputs) :
    v7493 s i = (if v8447 s i = 0 then 0 else 1) := by
  by_cases h : (v7398 s i) = 1
  · simp only [v7493, v8447, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7493, v8447, h, ↓reduceIte] using control_7492 s i

private theorem control_7494 (s : State) (i : Inputs) :
    v7494 s i = (if v8448 s i = 0 then 0 else 1) := by
  by_cases h : (v7395 s i) = 1
  · simp only [v7494, v8448, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7494, v8448, h, ↓reduceIte] using control_7493 s i

private theorem control_7495 (s : State) (i : Inputs) :
    v7495 s i = (if v8449 s i = 0 then 0 else 1) := by
  by_cases h : (v7391 s i) = 1
  · simp only [v7495, v8449, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7495, v8449, h, ↓reduceIte] using control_7494 s i

private theorem control_7496 (s : State) (i : Inputs) :
    v7496 s i = (if v8450 s i = 0 then 0 else 1) := by
  by_cases h : (v7387 s i) = 1
  · simp only [v7496, v8450, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7496, v8450, h, ↓reduceIte] using control_7495 s i

private theorem control_7497 (s : State) (i : Inputs) :
    v7497 s i = (if v8451 s i = 0 then 0 else 1) := by
  by_cases h : (v7383 s i) = 1
  · simp only [v7497, v8451, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7497, v8451, h, ↓reduceIte] using control_7496 s i

private theorem control_7498 (s : State) (i : Inputs) :
    v7498 s i = (if v8452 s i = 0 then 0 else 1) := by
  by_cases h : (v7379 s i) = 1
  · simp only [v7498, v8452, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7498, v8452, h, ↓reduceIte] using control_7497 s i

private theorem control_7499 (s : State) (i : Inputs) :
    v7499 s i = (if v8453 s i = 0 then 0 else 1) := by
  by_cases h : (v7375 s i) = 1
  · simp only [v7499, v8453, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7499, v8453, h, ↓reduceIte] using control_7498 s i

private theorem control_7500 (s : State) (i : Inputs) :
    v7500 s i = (if v8454 s i = 0 then 0 else 1) := by
  by_cases h : (v7371 s i) = 1
  · simp only [v7500, v8454, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7500, v8454, h, ↓reduceIte] using control_7499 s i

private theorem control_7501 (s : State) (i : Inputs) :
    v7501 s i = (if v8455 s i = 0 then 0 else 1) := by
  by_cases h : (v7367 s i) = 1
  · simp only [v7501, v8455, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7501, v8455, h, ↓reduceIte] using control_7500 s i

private theorem control_7502 (s : State) (i : Inputs) :
    v7502 s i = (if v8456 s i = 0 then 0 else 1) := by
  by_cases h : (v7363 s i) = 1
  · simp only [v7502, v8456, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7502, v8456, h, ↓reduceIte] using control_7501 s i

private theorem control_7503 (s : State) (i : Inputs) :
    v7503 s i = (if v8457 s i = 0 then 0 else 1) := by
  by_cases h : (v7359 s i) = 1
  · simp only [v7503, v8457, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7503, v8457, h, ↓reduceIte] using control_7502 s i

private theorem control_7504 (s : State) (i : Inputs) :
    v7504 s i = (if v8458 s i = 0 then 0 else 1) := by
  by_cases h : (v7355 s i) = 1
  · simp only [v7504, v8458, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7504, v8458, h, ↓reduceIte] using control_7503 s i

private theorem control_7505 (s : State) (i : Inputs) :
    v7505 s i = (if v8459 s i = 0 then 0 else 1) := by
  by_cases h : (v7351 s i) = 1
  · simp only [v7505, v8459, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7505, v8459, h, ↓reduceIte] using control_7504 s i

private theorem control_7506 (s : State) (i : Inputs) :
    v7506 s i = (if v8460 s i = 0 then 0 else 1) := by
  by_cases h : (v7347 s i) = 1
  · simp only [v7506, v8460, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7506, v8460, h, ↓reduceIte] using control_7505 s i

private theorem control_7507 (s : State) (i : Inputs) :
    v7507 s i = (if v8461 s i = 0 then 0 else 1) := by
  by_cases h : (v7343 s i) = 1
  · simp only [v7507, v8461, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7507, v8461, h, ↓reduceIte] using control_7506 s i

private theorem control_7508 (s : State) (i : Inputs) :
    v7508 s i = (if v8462 s i = 0 then 0 else 1) := by
  by_cases h : (v7339 s i) = 1
  · simp only [v7508, v8462, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7508, v8462, h, ↓reduceIte] using control_7507 s i

private theorem control_7509 (s : State) (i : Inputs) :
    v7509 s i = (if v8463 s i = 0 then 0 else 1) := by
  by_cases h : (v7335 s i) = 1
  · simp only [v7509, v8463, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7509, v8463, h, ↓reduceIte] using control_7508 s i

private theorem control_7510 (s : State) (i : Inputs) :
    v7510 s i = (if v8464 s i = 0 then 0 else 1) := by
  by_cases h : (v7331 s i) = 1
  · simp only [v7510, v8464, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7510, v8464, h, ↓reduceIte] using control_7509 s i

private theorem control_7511 (s : State) (i : Inputs) :
    v7511 s i = (if v8465 s i = 0 then 0 else 1) := by
  by_cases h : (v7327 s i) = 1
  · simp only [v7511, v8465, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7511, v8465, h, ↓reduceIte] using control_7510 s i

private theorem control_7512 (s : State) (i : Inputs) :
    v7512 s i = (if v8466 s i = 0 then 0 else 1) := by
  by_cases h : (v7323 s i) = 1
  · simp only [v7512, v8466, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7512, v8466, h, ↓reduceIte] using control_7511 s i

private theorem control_7513 (s : State) (i : Inputs) :
    v7513 s i = (if v8467 s i = 0 then 0 else 1) := by
  by_cases h : (v7319 s i) = 1
  · simp only [v7513, v8467, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7513, v8467, h, ↓reduceIte] using control_7512 s i

private theorem control_7514 (s : State) (i : Inputs) :
    v7514 s i = (if v8468 s i = 0 then 0 else 1) := by
  by_cases h : (v7315 s i) = 1
  · simp only [v7514, v8468, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7514, v8468, h, ↓reduceIte] using control_7513 s i

private theorem control_7515 (s : State) (i : Inputs) :
    v7515 s i = (if v8469 s i = 0 then 0 else 1) := by
  by_cases h : (v7311 s i) = 1
  · simp only [v7515, v8469, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7515, v8469, h, ↓reduceIte] using control_7514 s i

private theorem control_7516 (s : State) (i : Inputs) :
    v7516 s i = (if v8470 s i = 0 then 0 else 1) := by
  by_cases h : (v7307 s i) = 1
  · simp only [v7516, v8470, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7516, v8470, h, ↓reduceIte] using control_7515 s i

private theorem control_7517 (s : State) (i : Inputs) :
    v7517 s i = (if v8471 s i = 0 then 0 else 1) := by
  by_cases h : (v7303 s i) = 1
  · simp only [v7517, v8471, h, ↓reduceIte, v4, v512, v32, v38, v42, v155, BitVec.reduceEq]
  · simpa only [v7517, v8471, h, ↓reduceIte] using control_7516 s i

theorem fetch_cancel_pc_select (s : State) (i : Inputs) :
    v7519 s i = (if v8473 s i = 0 then 0 else 1) := by
  exact control_7517 s i

#print axioms fetch_cancel_pc_select
end RiscvMiniProofs
