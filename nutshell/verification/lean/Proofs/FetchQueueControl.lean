import Proofs.FrontendDequeueHandshake
namespace NutShellProofs
open nNutCore

/-- Unlike the backend ring, the fetch FIFO uses all four slots and a full bit. -/
def FetchRingSlots (head tail : BitVec 2) (full : Bool) : List (BitVec 2) :=
  (List.range (if head = tail ∧ full = true then 4 else (head - tail).toNat)).map
    (fun offset => tail + BitVec.ofNat 2 offset)

theorem fetch_ring_order_arithmetic : ∀ (head tail : BitVec 2) (full enq deq : Bool),
    (enq = true → ¬ (head = tail ∧ full = true)) →
    (deq = true → head ≠ tail ∨ full = true) →
    (FetchRingSlots (if enq then head + 1 else head) (if deq then tail + 1 else tail)
      (if enq != deq then enq else full)).map
      (fun slot => if enq = true ∧ slot = head then none else some slot) =
    (if deq then ((FetchRingSlots head tail full).map some).tail
      else (FetchRingSlots head tail full).map some) ++ (if enq then [none] else []) := by
  decide

theorem fetch_enqueue_not_full (s : State) (i : Inputs) (enqueue : v10241 s i = 1) :
    ¬ (s.g38.r1238_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fenq_5Fptr_5Fvalue =
      s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue ∧
      s.g38.r1240_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fmaybe_5Ffull = 1) := by
  rintro ⟨equal, full⟩
  simp [v10241, v2697, v2696, v2695, v2694, equal, full, v24] at enqueue

theorem fetch_dequeue_not_empty (s : State) (i : Inputs) (dequeue : v11083 s i = 1) :
    s.g38.r1238_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fenq_5Fptr_5Fvalue ≠
      s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue ∨
      s.g38.r1240_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fmaybe_5Ffull = 1 := by
  by_cases equal : s.g38.r1238_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fenq_5Fptr_5Fvalue =
      s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue
  · right
    rcases BitVec.eq_zero_or_eq_one s.g38.r1240_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fmaybe_5Ffull with zero | one
    · simp [v11083, v9801, v9800, v9799, v2694, equal, v9798, zero, v24] at dequeue
    · exact one
  · exact Or.inl equal

theorem fetch_enqueue_pointer_step (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (noRedirect : v14 s i = 0) :
    (step s i).g38.r1238_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fenq_5Fptr_5Fvalue =
      if v10241 s i = 1 then s.g38.r1238_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fenq_5Fptr_5Fvalue + 1
      else s.g38.r1238_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fenq_5Fptr_5Fvalue := by
  change v11049 s i = _
  simp [v11049, v10235, v0, reset, v11048, v11041, v11040, v18, v17,
    noRedirect, v16, v11047, v11046, v11045, v11043, v11044,
    low_add _ _ (by decide : 2 ≤ 3),
    BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 2 ≤ 2)]

theorem fetch_full_bit_step (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (noRedirect : v14 s i = 0) :
    (step s i).g38.r1240_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fmaybe_5Ffull =
      if v10241 s i ≠ v11083 s i then v10241 s i
      else s.g38.r1240_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fmaybe_5Ffull := by
  change v11094 s i = _
  simp [v11094, v10235, v0, reset, v11093, v11041, v11040, v18, v17,
    noRedirect, v16, v11092, v11091]

#print axioms fetch_ring_order_arithmetic
#print axioms fetch_enqueue_not_full
#print axioms fetch_dequeue_not_empty
#print axioms fetch_enqueue_pointer_step
#print axioms fetch_full_bit_step
end NutShellProofs
