import Proofs.StoreWriteback
import Proofs.DecodeBits
namespace NutShellProofs
open nNutCore
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
theorem reference_store_sb_not_v14578 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14578 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33583163) (by decide) matched
  simpa only [v14578, v14568, v14577, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33583163) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14583 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14583 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4261445631) (BitVec.ofNat 32 301990003) (by decide) matched
  simpa only [v14583, v14580, v14582, v14581, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 301990003) = (v14575 s i &&& (BitVec.ofNat 32 4261445631)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14589 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14589 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.allOnes 32) (BitVec.ofNat 32 273678451) (by decide) matched
  simpa only [v14589, v14588, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 273678451) = (v14575 s i &&& (BitVec.allOnes 32)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14595 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14595 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.allOnes 32) (BitVec.ofNat 32 807403635) (by decide) matched
  simpa only [v14595, v14594, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 807403635) = (v14575 s i &&& (BitVec.allOnes 32)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14601 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14601 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.allOnes 32) (BitVec.ofNat 32 270532723) (by decide) matched
  simpa only [v14601, v14600, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 270532723) = (v14575 s i &&& (BitVec.allOnes 32)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14613 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14613 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33579067) (by decide) matched
  simpa only [v14613, v14611, v14612, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33579067) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14621 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14621 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33574971) (by decide) matched
  simpa only [v14621, v14619, v14620, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33574971) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14629 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14629 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33570875) (by decide) matched
  simpa only [v14629, v14627, v14628, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33570875) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14637 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14637 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33554491) (by decide) matched
  simpa only [v14637, v14635, v14636, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33554491) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14645 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14645 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33583155) (by decide) matched
  simpa only [v14645, v14643, v14644, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33583155) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14653 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14653 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33579059) (by decide) matched
  simpa only [v14653, v14651, v14652, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33579059) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14661 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14661 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33574963) (by decide) matched
  simpa only [v14661, v14659, v14660, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33574963) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14669 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14669 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33570867) (by decide) matched
  simpa only [v14669, v14667, v14668, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33570867) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14677 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14677 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33566771) (by decide) matched
  simpa only [v14677, v14675, v14676, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33566771) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14685 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14685 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33562675) (by decide) matched
  simpa only [v14685, v14683, v14684, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33562675) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14693 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14693 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33558579) (by decide) matched
  simpa only [v14693, v14691, v14692, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33558579) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14701 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14701 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33554483) (by decide) matched
  simpa only [v14701, v14699, v14700, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33554483) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14710 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14710 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 12291) (by decide) matched
  simpa only [v14710, v14707, v14709, v14708, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 12291) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14718 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14718 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 24579) (by decide) matched
  simpa only [v14718, v14715, v14717, v14716, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 24579) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14725 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14725 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 1073762363) (by decide) matched
  simpa only [v14725, v14723, v14724, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 1073762363) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14733 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14733 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 1073741883) (by decide) matched
  simpa only [v14733, v14731, v14732, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 1073741883) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14741 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14741 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 20539) (by decide) matched
  simpa only [v14741, v14739, v14740, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 20539) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14749 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14749 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 4155) (by decide) matched
  simpa only [v14749, v14747, v14748, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 4155) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14757 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14757 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 59) (by decide) matched
  simpa only [v14757, v14755, v14756, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 59) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14765 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14765 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 1073762355) (by decide) matched
  simpa only [v14765, v14763, v14764, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 1073762355) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14773 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14773 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 20531) (by decide) matched
  simpa only [v14773, v14771, v14772, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 20531) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14781 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14781 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 4147) (by decide) matched
  simpa only [v14781, v14779, v14780, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 4147) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14789 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14789 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 1073762331) (by decide) matched
  simpa only [v14789, v14787, v14788, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 1073762331) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14796 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14796 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 20507) (by decide) matched
  simpa only [v14796, v14794, v14795, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 20507) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14803 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14803 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 4123) (by decide) matched
  simpa only [v14803, v14801, v14802, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 4123) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14811 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14811 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4227887231) (BitVec.ofNat 32 1073762323) (by decide) matched
  simpa only [v14811, v14808, v14810, v14809, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 1073762323) = (v14575 s i &&& (BitVec.ofNat 32 4227887231)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14818 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14818 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4227887231) (BitVec.ofNat 32 20499) (by decide) matched
  simpa only [v14818, v14816, v14817, v14809, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 20499) = (v14575 s i &&& (BitVec.ofNat 32 4227887231)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14825 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14825 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4227887231) (BitVec.ofNat 32 4115) (by decide) matched
  simpa only [v14825, v14823, v14824, v14809, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 4115) = (v14575 s i &&& (BitVec.ofNat 32 4227887231)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14833 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14833 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 27) (by decide) matched
  simpa only [v14833, v14830, v14832, v14831, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 27) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14841 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14841 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 15) (by decide) matched
  simpa only [v14841, v14838, v14840, v14839, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 15) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14847 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14847 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.allOnes 32) (BitVec.ofNat 32 115) (by decide) matched
  simpa only [v14847, v14846, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 115) = (v14575 s i &&& (BitVec.allOnes 32)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14853 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14853 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.allOnes 32) (BitVec.ofNat 32 1048691) (by decide) matched
  simpa only [v14853, v14852, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 1048691) = (v14575 s i &&& (BitVec.allOnes 32)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14861 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14861 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 20483) (by decide) matched
  simpa only [v14861, v14858, v14860, v14859, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 20483) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14869 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14869 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 16387) (by decide) matched
  simpa only [v14869, v14866, v14868, v14867, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 16387) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14877 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14877 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 8195) (by decide) matched
  simpa only [v14877, v14874, v14876, v14875, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 8195) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14885 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14885 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 4099) (by decide) matched
  simpa only [v14885, v14882, v14884, v14883, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 4099) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14893 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14893 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 3) (by decide) matched
  simpa only [v14893, v14890, v14892, v14891, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 3) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14901 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14901 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 103) (by decide) matched
  simpa only [v14901, v14898, v14900, v14899, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 103) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14909 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14909 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 127) (BitVec.ofNat 32 111) (by decide) matched
  simpa only [v14909, v14906, v14908, v14907, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 111) = (v14575 s i &&& (BitVec.ofNat 32 127)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14917 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14917 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 1073762355) (by decide) matched
  simpa only [v14917, v14915, v14916, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 1073762355) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14925 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14925 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 1073741875) (by decide) matched
  simpa only [v14925, v14923, v14924, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 1073741875) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14933 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14933 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 20531) (by decide) matched
  simpa only [v14933, v14931, v14932, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 20531) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14941 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14941 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 4147) (by decide) matched
  simpa only [v14941, v14939, v14940, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 4147) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14949 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14949 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 16435) (by decide) matched
  simpa only [v14949, v14947, v14948, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 16435) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14957 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14957 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 24627) (by decide) matched
  simpa only [v14957, v14955, v14956, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 24627) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14965 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14965 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 28723) (by decide) matched
  simpa only [v14965, v14963, v14964, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 28723) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14973 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14973 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 12339) (by decide) matched
  simpa only [v14973, v14971, v14972, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 12339) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14981 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14981 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 8243) (by decide) matched
  simpa only [v14981, v14979, v14980, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 8243) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14989 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14989 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 51) (by decide) matched
  simpa only [v14989, v14987, v14988, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 51) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v14998 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v14998 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 127) (BitVec.ofNat 32 23) (by decide) matched
  simpa only [v14998, v14995, v14997, v14996, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 23) = (v14575 s i &&& (BitVec.ofNat 32 127)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v15004 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v15004 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 127) (BitVec.ofNat 32 55) (by decide) matched
  simpa only [v15004, v15001, v15003, v15002, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 55) = (v14575 s i &&& (BitVec.ofNat 32 127)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v15009 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v15009 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4227887231) (BitVec.ofNat 32 1073762323) (by decide) matched
  simpa only [v15009, v15007, v15008, v14809, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 1073762323) = (v14575 s i &&& (BitVec.ofNat 32 4227887231)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v15016 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v15016 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4227887231) (BitVec.ofNat 32 20499) (by decide) matched
  simpa only [v15016, v15014, v15015, v14809, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 20499) = (v14575 s i &&& (BitVec.ofNat 32 4227887231)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v15023 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v15023 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 4227887231) (BitVec.ofNat 32 4115) (by decide) matched
  simpa only [v15023, v15021, v15022, v14809, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 4115) = (v14575 s i &&& (BitVec.ofNat 32 4227887231)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v15031 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v15031 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 16403) (by decide) matched
  simpa only [v15031, v15028, v15030, v15029, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 16403) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v15039 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v15039 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 24595) (by decide) matched
  simpa only [v15039, v15036, v15038, v15037, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 24595) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v15047 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v15047 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 28691) (by decide) matched
  simpa only [v15047, v15044, v15046, v15045, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 28691) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v15055 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v15055 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 12307) (by decide) matched
  simpa only [v15055, v15052, v15054, v15053, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 12307) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v15063 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v15063 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 8211) (by decide) matched
  simpa only [v15063, v15060, v15062, v15061, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 8211) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v15071 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v15071 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 19) (by decide) matched
  simpa only [v15071, v15068, v15070, v15069, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 19) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v15160 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v15160 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 12323) (by decide) matched
  simpa only [v15160, v15157, v15159, v15158, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 12323) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v15174 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v15174 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 8227) (by decide) matched
  simpa only [v15174, v15171, v15173, v15172, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 8227) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v15180 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v15180 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 4131) (by decide) matched
  simpa only [v15180, v15177, v15179, v15178, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 4131) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v15192 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v15192 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 28771) (by decide) matched
  simpa only [v15192, v15189, v15191, v15190, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 28771) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v15199 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v15199 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 20579) (by decide) matched
  simpa only [v15199, v15196, v15198, v15197, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 20579) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v15206 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v15206 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 24675) (by decide) matched
  simpa only [v15206, v15203, v15205, v15204, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 24675) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v15213 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v15213 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 16483) (by decide) matched
  simpa only [v15213, v15210, v15212, v15211, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 16483) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v15220 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v15220 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 4195) (by decide) matched
  simpa only [v15220, v15217, v15219, v15218, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 4195) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sb_not_v15227 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 35) :
    v15227 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 35) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 99) (by decide) matched
  simpa only [v15227, v15224, v15226, v15225, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 99) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14578 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14578 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33583163) (by decide) matched
  simpa only [v14578, v14568, v14577, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33583163) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14583 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14583 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4261445631) (BitVec.ofNat 32 301990003) (by decide) matched
  simpa only [v14583, v14580, v14582, v14581, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 301990003) = (v14575 s i &&& (BitVec.ofNat 32 4261445631)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14589 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14589 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.allOnes 32) (BitVec.ofNat 32 273678451) (by decide) matched
  simpa only [v14589, v14588, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 273678451) = (v14575 s i &&& (BitVec.allOnes 32)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14595 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14595 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.allOnes 32) (BitVec.ofNat 32 807403635) (by decide) matched
  simpa only [v14595, v14594, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 807403635) = (v14575 s i &&& (BitVec.allOnes 32)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14601 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14601 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.allOnes 32) (BitVec.ofNat 32 270532723) (by decide) matched
  simpa only [v14601, v14600, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 270532723) = (v14575 s i &&& (BitVec.allOnes 32)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14613 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14613 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33579067) (by decide) matched
  simpa only [v14613, v14611, v14612, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33579067) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14621 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14621 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33574971) (by decide) matched
  simpa only [v14621, v14619, v14620, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33574971) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14629 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14629 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33570875) (by decide) matched
  simpa only [v14629, v14627, v14628, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33570875) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14637 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14637 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33554491) (by decide) matched
  simpa only [v14637, v14635, v14636, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33554491) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14645 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14645 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33583155) (by decide) matched
  simpa only [v14645, v14643, v14644, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33583155) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14653 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14653 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33579059) (by decide) matched
  simpa only [v14653, v14651, v14652, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33579059) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14661 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14661 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33574963) (by decide) matched
  simpa only [v14661, v14659, v14660, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33574963) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14669 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14669 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33570867) (by decide) matched
  simpa only [v14669, v14667, v14668, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33570867) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14677 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14677 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33566771) (by decide) matched
  simpa only [v14677, v14675, v14676, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33566771) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14685 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14685 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33562675) (by decide) matched
  simpa only [v14685, v14683, v14684, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33562675) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14693 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14693 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33558579) (by decide) matched
  simpa only [v14693, v14691, v14692, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33558579) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14701 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14701 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33554483) (by decide) matched
  simpa only [v14701, v14699, v14700, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33554483) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14710 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14710 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 12291) (by decide) matched
  simpa only [v14710, v14707, v14709, v14708, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 12291) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14718 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14718 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 24579) (by decide) matched
  simpa only [v14718, v14715, v14717, v14716, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 24579) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14725 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14725 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 1073762363) (by decide) matched
  simpa only [v14725, v14723, v14724, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 1073762363) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14733 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14733 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 1073741883) (by decide) matched
  simpa only [v14733, v14731, v14732, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 1073741883) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14741 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14741 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 20539) (by decide) matched
  simpa only [v14741, v14739, v14740, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 20539) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14749 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14749 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 4155) (by decide) matched
  simpa only [v14749, v14747, v14748, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 4155) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14757 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14757 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 59) (by decide) matched
  simpa only [v14757, v14755, v14756, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 59) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14765 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14765 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 1073762355) (by decide) matched
  simpa only [v14765, v14763, v14764, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 1073762355) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14773 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14773 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 20531) (by decide) matched
  simpa only [v14773, v14771, v14772, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 20531) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14781 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14781 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 4147) (by decide) matched
  simpa only [v14781, v14779, v14780, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 4147) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14789 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14789 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 1073762331) (by decide) matched
  simpa only [v14789, v14787, v14788, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 1073762331) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14796 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14796 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 20507) (by decide) matched
  simpa only [v14796, v14794, v14795, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 20507) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14803 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14803 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 4123) (by decide) matched
  simpa only [v14803, v14801, v14802, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 4123) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14811 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14811 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4227887231) (BitVec.ofNat 32 1073762323) (by decide) matched
  simpa only [v14811, v14808, v14810, v14809, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 1073762323) = (v14575 s i &&& (BitVec.ofNat 32 4227887231)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14818 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14818 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4227887231) (BitVec.ofNat 32 20499) (by decide) matched
  simpa only [v14818, v14816, v14817, v14809, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 20499) = (v14575 s i &&& (BitVec.ofNat 32 4227887231)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14825 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14825 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4227887231) (BitVec.ofNat 32 4115) (by decide) matched
  simpa only [v14825, v14823, v14824, v14809, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 4115) = (v14575 s i &&& (BitVec.ofNat 32 4227887231)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14833 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14833 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 27) (by decide) matched
  simpa only [v14833, v14830, v14832, v14831, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 27) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14841 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14841 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 15) (by decide) matched
  simpa only [v14841, v14838, v14840, v14839, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 15) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14847 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14847 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.allOnes 32) (BitVec.ofNat 32 115) (by decide) matched
  simpa only [v14847, v14846, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 115) = (v14575 s i &&& (BitVec.allOnes 32)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14853 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14853 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.allOnes 32) (BitVec.ofNat 32 1048691) (by decide) matched
  simpa only [v14853, v14852, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 1048691) = (v14575 s i &&& (BitVec.allOnes 32)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14861 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14861 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 20483) (by decide) matched
  simpa only [v14861, v14858, v14860, v14859, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 20483) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14869 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14869 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 16387) (by decide) matched
  simpa only [v14869, v14866, v14868, v14867, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 16387) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14877 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14877 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 8195) (by decide) matched
  simpa only [v14877, v14874, v14876, v14875, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 8195) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14885 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14885 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 4099) (by decide) matched
  simpa only [v14885, v14882, v14884, v14883, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 4099) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14893 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14893 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 3) (by decide) matched
  simpa only [v14893, v14890, v14892, v14891, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 3) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14901 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14901 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 103) (by decide) matched
  simpa only [v14901, v14898, v14900, v14899, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 103) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14909 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14909 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 127) (BitVec.ofNat 32 111) (by decide) matched
  simpa only [v14909, v14906, v14908, v14907, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 111) = (v14575 s i &&& (BitVec.ofNat 32 127)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14917 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14917 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 1073762355) (by decide) matched
  simpa only [v14917, v14915, v14916, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 1073762355) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14925 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14925 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 1073741875) (by decide) matched
  simpa only [v14925, v14923, v14924, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 1073741875) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14933 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14933 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 20531) (by decide) matched
  simpa only [v14933, v14931, v14932, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 20531) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14941 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14941 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 4147) (by decide) matched
  simpa only [v14941, v14939, v14940, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 4147) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14949 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14949 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 16435) (by decide) matched
  simpa only [v14949, v14947, v14948, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 16435) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14957 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14957 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 24627) (by decide) matched
  simpa only [v14957, v14955, v14956, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 24627) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14965 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14965 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 28723) (by decide) matched
  simpa only [v14965, v14963, v14964, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 28723) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14973 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14973 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 12339) (by decide) matched
  simpa only [v14973, v14971, v14972, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 12339) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14981 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14981 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 8243) (by decide) matched
  simpa only [v14981, v14979, v14980, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 8243) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14989 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14989 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 51) (by decide) matched
  simpa only [v14989, v14987, v14988, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 51) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v14998 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v14998 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 127) (BitVec.ofNat 32 23) (by decide) matched
  simpa only [v14998, v14995, v14997, v14996, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 23) = (v14575 s i &&& (BitVec.ofNat 32 127)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v15004 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v15004 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 127) (BitVec.ofNat 32 55) (by decide) matched
  simpa only [v15004, v15001, v15003, v15002, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 55) = (v14575 s i &&& (BitVec.ofNat 32 127)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v15009 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v15009 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4227887231) (BitVec.ofNat 32 1073762323) (by decide) matched
  simpa only [v15009, v15007, v15008, v14809, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 1073762323) = (v14575 s i &&& (BitVec.ofNat 32 4227887231)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v15016 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v15016 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4227887231) (BitVec.ofNat 32 20499) (by decide) matched
  simpa only [v15016, v15014, v15015, v14809, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 20499) = (v14575 s i &&& (BitVec.ofNat 32 4227887231)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v15023 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v15023 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 4227887231) (BitVec.ofNat 32 4115) (by decide) matched
  simpa only [v15023, v15021, v15022, v14809, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 4115) = (v14575 s i &&& (BitVec.ofNat 32 4227887231)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v15031 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v15031 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 16403) (by decide) matched
  simpa only [v15031, v15028, v15030, v15029, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 16403) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v15039 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v15039 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 24595) (by decide) matched
  simpa only [v15039, v15036, v15038, v15037, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 24595) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v15047 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v15047 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 28691) (by decide) matched
  simpa only [v15047, v15044, v15046, v15045, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 28691) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v15055 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v15055 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 12307) (by decide) matched
  simpa only [v15055, v15052, v15054, v15053, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 12307) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v15063 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v15063 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 8211) (by decide) matched
  simpa only [v15063, v15060, v15062, v15061, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 8211) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v15071 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v15071 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 19) (by decide) matched
  simpa only [v15071, v15068, v15070, v15069, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 19) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v15160 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v15160 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 12323) (by decide) matched
  simpa only [v15160, v15157, v15159, v15158, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 12323) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v15174 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v15174 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 8227) (by decide) matched
  simpa only [v15174, v15171, v15173, v15172, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 8227) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v15186 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v15186 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 35) (by decide) matched
  simpa only [v15186, v15183, v15185, v15184, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 35) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v15192 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v15192 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 28771) (by decide) matched
  simpa only [v15192, v15189, v15191, v15190, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 28771) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v15199 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v15199 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 20579) (by decide) matched
  simpa only [v15199, v15196, v15198, v15197, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 20579) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v15206 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v15206 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 24675) (by decide) matched
  simpa only [v15206, v15203, v15205, v15204, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 24675) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v15213 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v15213 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 16483) (by decide) matched
  simpa only [v15213, v15210, v15212, v15211, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 16483) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v15220 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v15220 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 4195) (by decide) matched
  simpa only [v15220, v15217, v15219, v15218, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 4195) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sh_not_v15227 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4131) :
    v15227 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 4131) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 99) (by decide) matched
  simpa only [v15227, v15224, v15226, v15225, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 99) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14578 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14578 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33583163) (by decide) matched
  simpa only [v14578, v14568, v14577, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33583163) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14583 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14583 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4261445631) (BitVec.ofNat 32 301990003) (by decide) matched
  simpa only [v14583, v14580, v14582, v14581, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 301990003) = (v14575 s i &&& (BitVec.ofNat 32 4261445631)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14589 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14589 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.allOnes 32) (BitVec.ofNat 32 273678451) (by decide) matched
  simpa only [v14589, v14588, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 273678451) = (v14575 s i &&& (BitVec.allOnes 32)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14595 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14595 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.allOnes 32) (BitVec.ofNat 32 807403635) (by decide) matched
  simpa only [v14595, v14594, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 807403635) = (v14575 s i &&& (BitVec.allOnes 32)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14601 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14601 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.allOnes 32) (BitVec.ofNat 32 270532723) (by decide) matched
  simpa only [v14601, v14600, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 270532723) = (v14575 s i &&& (BitVec.allOnes 32)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14613 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14613 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33579067) (by decide) matched
  simpa only [v14613, v14611, v14612, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33579067) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14621 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14621 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33574971) (by decide) matched
  simpa only [v14621, v14619, v14620, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33574971) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14629 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14629 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33570875) (by decide) matched
  simpa only [v14629, v14627, v14628, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33570875) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14637 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14637 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33554491) (by decide) matched
  simpa only [v14637, v14635, v14636, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33554491) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14645 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14645 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33583155) (by decide) matched
  simpa only [v14645, v14643, v14644, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33583155) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14653 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14653 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33579059) (by decide) matched
  simpa only [v14653, v14651, v14652, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33579059) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14661 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14661 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33574963) (by decide) matched
  simpa only [v14661, v14659, v14660, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33574963) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14669 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14669 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33570867) (by decide) matched
  simpa only [v14669, v14667, v14668, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33570867) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14677 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14677 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33566771) (by decide) matched
  simpa only [v14677, v14675, v14676, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33566771) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14685 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14685 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33562675) (by decide) matched
  simpa only [v14685, v14683, v14684, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33562675) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14693 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14693 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33558579) (by decide) matched
  simpa only [v14693, v14691, v14692, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33558579) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14701 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14701 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33554483) (by decide) matched
  simpa only [v14701, v14699, v14700, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33554483) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14710 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14710 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 12291) (by decide) matched
  simpa only [v14710, v14707, v14709, v14708, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 12291) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14718 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14718 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 24579) (by decide) matched
  simpa only [v14718, v14715, v14717, v14716, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 24579) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14725 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14725 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 1073762363) (by decide) matched
  simpa only [v14725, v14723, v14724, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 1073762363) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14733 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14733 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 1073741883) (by decide) matched
  simpa only [v14733, v14731, v14732, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 1073741883) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14741 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14741 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 20539) (by decide) matched
  simpa only [v14741, v14739, v14740, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 20539) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14749 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14749 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 4155) (by decide) matched
  simpa only [v14749, v14747, v14748, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 4155) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14757 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14757 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 59) (by decide) matched
  simpa only [v14757, v14755, v14756, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 59) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14765 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14765 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 1073762355) (by decide) matched
  simpa only [v14765, v14763, v14764, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 1073762355) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14773 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14773 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 20531) (by decide) matched
  simpa only [v14773, v14771, v14772, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 20531) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14781 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14781 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 4147) (by decide) matched
  simpa only [v14781, v14779, v14780, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 4147) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14789 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14789 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 1073762331) (by decide) matched
  simpa only [v14789, v14787, v14788, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 1073762331) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14796 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14796 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 20507) (by decide) matched
  simpa only [v14796, v14794, v14795, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 20507) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14803 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14803 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 4123) (by decide) matched
  simpa only [v14803, v14801, v14802, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 4123) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14811 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14811 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4227887231) (BitVec.ofNat 32 1073762323) (by decide) matched
  simpa only [v14811, v14808, v14810, v14809, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 1073762323) = (v14575 s i &&& (BitVec.ofNat 32 4227887231)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14818 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14818 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4227887231) (BitVec.ofNat 32 20499) (by decide) matched
  simpa only [v14818, v14816, v14817, v14809, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 20499) = (v14575 s i &&& (BitVec.ofNat 32 4227887231)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14825 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14825 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4227887231) (BitVec.ofNat 32 4115) (by decide) matched
  simpa only [v14825, v14823, v14824, v14809, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 4115) = (v14575 s i &&& (BitVec.ofNat 32 4227887231)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14833 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14833 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 27) (by decide) matched
  simpa only [v14833, v14830, v14832, v14831, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 27) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14841 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14841 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 15) (by decide) matched
  simpa only [v14841, v14838, v14840, v14839, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 15) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14847 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14847 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.allOnes 32) (BitVec.ofNat 32 115) (by decide) matched
  simpa only [v14847, v14846, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 115) = (v14575 s i &&& (BitVec.allOnes 32)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14853 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14853 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.allOnes 32) (BitVec.ofNat 32 1048691) (by decide) matched
  simpa only [v14853, v14852, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 1048691) = (v14575 s i &&& (BitVec.allOnes 32)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14861 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14861 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 20483) (by decide) matched
  simpa only [v14861, v14858, v14860, v14859, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 20483) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14869 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14869 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 16387) (by decide) matched
  simpa only [v14869, v14866, v14868, v14867, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 16387) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14877 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14877 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 8195) (by decide) matched
  simpa only [v14877, v14874, v14876, v14875, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 8195) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14885 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14885 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 4099) (by decide) matched
  simpa only [v14885, v14882, v14884, v14883, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 4099) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14893 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14893 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 3) (by decide) matched
  simpa only [v14893, v14890, v14892, v14891, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 3) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14901 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14901 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 103) (by decide) matched
  simpa only [v14901, v14898, v14900, v14899, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 103) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14909 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14909 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 127) (BitVec.ofNat 32 111) (by decide) matched
  simpa only [v14909, v14906, v14908, v14907, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 111) = (v14575 s i &&& (BitVec.ofNat 32 127)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14917 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14917 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 1073762355) (by decide) matched
  simpa only [v14917, v14915, v14916, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 1073762355) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14925 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14925 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 1073741875) (by decide) matched
  simpa only [v14925, v14923, v14924, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 1073741875) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14933 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14933 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 20531) (by decide) matched
  simpa only [v14933, v14931, v14932, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 20531) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14941 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14941 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 4147) (by decide) matched
  simpa only [v14941, v14939, v14940, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 4147) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14949 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14949 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 16435) (by decide) matched
  simpa only [v14949, v14947, v14948, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 16435) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14957 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14957 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 24627) (by decide) matched
  simpa only [v14957, v14955, v14956, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 24627) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14965 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14965 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 28723) (by decide) matched
  simpa only [v14965, v14963, v14964, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 28723) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14973 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14973 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 12339) (by decide) matched
  simpa only [v14973, v14971, v14972, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 12339) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14981 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14981 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 8243) (by decide) matched
  simpa only [v14981, v14979, v14980, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 8243) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14989 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14989 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 51) (by decide) matched
  simpa only [v14989, v14987, v14988, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 51) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v14998 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v14998 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 127) (BitVec.ofNat 32 23) (by decide) matched
  simpa only [v14998, v14995, v14997, v14996, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 23) = (v14575 s i &&& (BitVec.ofNat 32 127)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v15004 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v15004 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 127) (BitVec.ofNat 32 55) (by decide) matched
  simpa only [v15004, v15001, v15003, v15002, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 55) = (v14575 s i &&& (BitVec.ofNat 32 127)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v15009 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v15009 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4227887231) (BitVec.ofNat 32 1073762323) (by decide) matched
  simpa only [v15009, v15007, v15008, v14809, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 1073762323) = (v14575 s i &&& (BitVec.ofNat 32 4227887231)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v15016 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v15016 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4227887231) (BitVec.ofNat 32 20499) (by decide) matched
  simpa only [v15016, v15014, v15015, v14809, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 20499) = (v14575 s i &&& (BitVec.ofNat 32 4227887231)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v15023 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v15023 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 4227887231) (BitVec.ofNat 32 4115) (by decide) matched
  simpa only [v15023, v15021, v15022, v14809, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 4115) = (v14575 s i &&& (BitVec.ofNat 32 4227887231)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v15031 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v15031 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 16403) (by decide) matched
  simpa only [v15031, v15028, v15030, v15029, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 16403) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v15039 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v15039 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 24595) (by decide) matched
  simpa only [v15039, v15036, v15038, v15037, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 24595) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v15047 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v15047 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 28691) (by decide) matched
  simpa only [v15047, v15044, v15046, v15045, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 28691) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v15055 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v15055 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 12307) (by decide) matched
  simpa only [v15055, v15052, v15054, v15053, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 12307) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v15063 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v15063 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 8211) (by decide) matched
  simpa only [v15063, v15060, v15062, v15061, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 8211) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v15071 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v15071 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 19) (by decide) matched
  simpa only [v15071, v15068, v15070, v15069, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 19) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v15160 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v15160 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 12323) (by decide) matched
  simpa only [v15160, v15157, v15159, v15158, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 12323) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v15180 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v15180 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 4131) (by decide) matched
  simpa only [v15180, v15177, v15179, v15178, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 4131) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v15186 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v15186 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 35) (by decide) matched
  simpa only [v15186, v15183, v15185, v15184, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 35) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v15192 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v15192 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 28771) (by decide) matched
  simpa only [v15192, v15189, v15191, v15190, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 28771) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v15199 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v15199 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 20579) (by decide) matched
  simpa only [v15199, v15196, v15198, v15197, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 20579) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v15206 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v15206 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 24675) (by decide) matched
  simpa only [v15206, v15203, v15205, v15204, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 24675) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v15213 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v15213 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 16483) (by decide) matched
  simpa only [v15213, v15210, v15212, v15211, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 16483) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v15220 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v15220 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 4195) (by decide) matched
  simpa only [v15220, v15217, v15219, v15218, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 4195) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sw_not_v15227 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 8227) :
    v15227 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 8227) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 99) (by decide) matched
  simpa only [v15227, v15224, v15226, v15225, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 99) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14578 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14578 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33583163) (by decide) matched
  simpa only [v14578, v14568, v14577, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33583163) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14583 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14583 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4261445631) (BitVec.ofNat 32 301990003) (by decide) matched
  simpa only [v14583, v14580, v14582, v14581, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 301990003) = (v14575 s i &&& (BitVec.ofNat 32 4261445631)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14589 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14589 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.allOnes 32) (BitVec.ofNat 32 273678451) (by decide) matched
  simpa only [v14589, v14588, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 273678451) = (v14575 s i &&& (BitVec.allOnes 32)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14595 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14595 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.allOnes 32) (BitVec.ofNat 32 807403635) (by decide) matched
  simpa only [v14595, v14594, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 807403635) = (v14575 s i &&& (BitVec.allOnes 32)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14601 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14601 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.allOnes 32) (BitVec.ofNat 32 270532723) (by decide) matched
  simpa only [v14601, v14600, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 270532723) = (v14575 s i &&& (BitVec.allOnes 32)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14613 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14613 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33579067) (by decide) matched
  simpa only [v14613, v14611, v14612, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33579067) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14621 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14621 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33574971) (by decide) matched
  simpa only [v14621, v14619, v14620, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33574971) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14629 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14629 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33570875) (by decide) matched
  simpa only [v14629, v14627, v14628, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33570875) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14637 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14637 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33554491) (by decide) matched
  simpa only [v14637, v14635, v14636, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33554491) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14645 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14645 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33583155) (by decide) matched
  simpa only [v14645, v14643, v14644, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33583155) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14653 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14653 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33579059) (by decide) matched
  simpa only [v14653, v14651, v14652, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33579059) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14661 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14661 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33574963) (by decide) matched
  simpa only [v14661, v14659, v14660, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33574963) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14669 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14669 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33570867) (by decide) matched
  simpa only [v14669, v14667, v14668, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33570867) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14677 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14677 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33566771) (by decide) matched
  simpa only [v14677, v14675, v14676, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33566771) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14685 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14685 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33562675) (by decide) matched
  simpa only [v14685, v14683, v14684, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33562675) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14693 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14693 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33558579) (by decide) matched
  simpa only [v14693, v14691, v14692, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33558579) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14701 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14701 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 33554483) (by decide) matched
  simpa only [v14701, v14699, v14700, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 33554483) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14710 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14710 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 12291) (by decide) matched
  simpa only [v14710, v14707, v14709, v14708, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 12291) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14718 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14718 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 24579) (by decide) matched
  simpa only [v14718, v14715, v14717, v14716, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 24579) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14725 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14725 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 1073762363) (by decide) matched
  simpa only [v14725, v14723, v14724, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 1073762363) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14733 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14733 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 1073741883) (by decide) matched
  simpa only [v14733, v14731, v14732, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 1073741883) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14741 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14741 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 20539) (by decide) matched
  simpa only [v14741, v14739, v14740, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 20539) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14749 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14749 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 4155) (by decide) matched
  simpa only [v14749, v14747, v14748, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 4155) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14757 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14757 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 59) (by decide) matched
  simpa only [v14757, v14755, v14756, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 59) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14765 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14765 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 1073762355) (by decide) matched
  simpa only [v14765, v14763, v14764, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 1073762355) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14773 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14773 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 20531) (by decide) matched
  simpa only [v14773, v14771, v14772, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 20531) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14781 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14781 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 4147) (by decide) matched
  simpa only [v14781, v14779, v14780, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 4147) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14789 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14789 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 1073762331) (by decide) matched
  simpa only [v14789, v14787, v14788, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 1073762331) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14796 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14796 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 20507) (by decide) matched
  simpa only [v14796, v14794, v14795, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 20507) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14803 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14803 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 4123) (by decide) matched
  simpa only [v14803, v14801, v14802, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 4123) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14811 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14811 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4227887231) (BitVec.ofNat 32 1073762323) (by decide) matched
  simpa only [v14811, v14808, v14810, v14809, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 1073762323) = (v14575 s i &&& (BitVec.ofNat 32 4227887231)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14818 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14818 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4227887231) (BitVec.ofNat 32 20499) (by decide) matched
  simpa only [v14818, v14816, v14817, v14809, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 20499) = (v14575 s i &&& (BitVec.ofNat 32 4227887231)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14825 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14825 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4227887231) (BitVec.ofNat 32 4115) (by decide) matched
  simpa only [v14825, v14823, v14824, v14809, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 4115) = (v14575 s i &&& (BitVec.ofNat 32 4227887231)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14833 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14833 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 27) (by decide) matched
  simpa only [v14833, v14830, v14832, v14831, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 27) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14841 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14841 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 15) (by decide) matched
  simpa only [v14841, v14838, v14840, v14839, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 15) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14847 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14847 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.allOnes 32) (BitVec.ofNat 32 115) (by decide) matched
  simpa only [v14847, v14846, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 115) = (v14575 s i &&& (BitVec.allOnes 32)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14853 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14853 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.allOnes 32) (BitVec.ofNat 32 1048691) (by decide) matched
  simpa only [v14853, v14852, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 1048691) = (v14575 s i &&& (BitVec.allOnes 32)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14861 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14861 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 20483) (by decide) matched
  simpa only [v14861, v14858, v14860, v14859, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 20483) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14869 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14869 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 16387) (by decide) matched
  simpa only [v14869, v14866, v14868, v14867, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 16387) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14877 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14877 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 8195) (by decide) matched
  simpa only [v14877, v14874, v14876, v14875, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 8195) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14885 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14885 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 4099) (by decide) matched
  simpa only [v14885, v14882, v14884, v14883, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 4099) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14893 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14893 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 3) (by decide) matched
  simpa only [v14893, v14890, v14892, v14891, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 3) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14901 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14901 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 103) (by decide) matched
  simpa only [v14901, v14898, v14900, v14899, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 103) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14909 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14909 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 127) (BitVec.ofNat 32 111) (by decide) matched
  simpa only [v14909, v14906, v14908, v14907, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 111) = (v14575 s i &&& (BitVec.ofNat 32 127)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14917 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14917 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 1073762355) (by decide) matched
  simpa only [v14917, v14915, v14916, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 1073762355) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14925 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14925 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 1073741875) (by decide) matched
  simpa only [v14925, v14923, v14924, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 1073741875) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14933 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14933 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 20531) (by decide) matched
  simpa only [v14933, v14931, v14932, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 20531) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14941 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14941 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 4147) (by decide) matched
  simpa only [v14941, v14939, v14940, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 4147) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14949 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14949 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 16435) (by decide) matched
  simpa only [v14949, v14947, v14948, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 16435) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14957 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14957 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 24627) (by decide) matched
  simpa only [v14957, v14955, v14956, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 24627) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14965 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14965 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 28723) (by decide) matched
  simpa only [v14965, v14963, v14964, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 28723) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14973 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14973 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 12339) (by decide) matched
  simpa only [v14973, v14971, v14972, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 12339) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14981 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14981 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 8243) (by decide) matched
  simpa only [v14981, v14979, v14980, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 8243) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14989 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14989 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4261441663) (BitVec.ofNat 32 51) (by decide) matched
  simpa only [v14989, v14987, v14988, v14576, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 51) = (v14575 s i &&& (BitVec.ofNat 32 4261441663)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v14998 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v14998 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 127) (BitVec.ofNat 32 23) (by decide) matched
  simpa only [v14998, v14995, v14997, v14996, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 23) = (v14575 s i &&& (BitVec.ofNat 32 127)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v15004 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v15004 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 127) (BitVec.ofNat 32 55) (by decide) matched
  simpa only [v15004, v15001, v15003, v15002, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 55) = (v14575 s i &&& (BitVec.ofNat 32 127)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v15009 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v15009 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4227887231) (BitVec.ofNat 32 1073762323) (by decide) matched
  simpa only [v15009, v15007, v15008, v14809, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 1073762323) = (v14575 s i &&& (BitVec.ofNat 32 4227887231)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v15016 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v15016 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4227887231) (BitVec.ofNat 32 20499) (by decide) matched
  simpa only [v15016, v15014, v15015, v14809, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 20499) = (v14575 s i &&& (BitVec.ofNat 32 4227887231)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v15023 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v15023 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 4227887231) (BitVec.ofNat 32 4115) (by decide) matched
  simpa only [v15023, v15021, v15022, v14809, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 4115) = (v14575 s i &&& (BitVec.ofNat 32 4227887231)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v15031 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v15031 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 16403) (by decide) matched
  simpa only [v15031, v15028, v15030, v15029, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 16403) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v15039 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v15039 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 24595) (by decide) matched
  simpa only [v15039, v15036, v15038, v15037, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 24595) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v15047 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v15047 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 28691) (by decide) matched
  simpa only [v15047, v15044, v15046, v15045, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 28691) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v15055 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v15055 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 12307) (by decide) matched
  simpa only [v15055, v15052, v15054, v15053, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 12307) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v15063 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v15063 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 8211) (by decide) matched
  simpa only [v15063, v15060, v15062, v15061, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 8211) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v15071 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v15071 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 19) (by decide) matched
  simpa only [v15071, v15068, v15070, v15069, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 19) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v15174 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v15174 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 8227) (by decide) matched
  simpa only [v15174, v15171, v15173, v15172, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 8227) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v15180 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v15180 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 4131) (by decide) matched
  simpa only [v15180, v15177, v15179, v15178, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 4131) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v15186 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v15186 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 35) (by decide) matched
  simpa only [v15186, v15183, v15185, v15184, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 35) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v15192 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v15192 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 28771) (by decide) matched
  simpa only [v15192, v15189, v15191, v15190, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 28771) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v15199 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v15199 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 20579) (by decide) matched
  simpa only [v15199, v15196, v15198, v15197, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 20579) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v15206 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v15206 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 24675) (by decide) matched
  simpa only [v15206, v15203, v15205, v15204, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 24675) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v15213 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v15213 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 16483) (by decide) matched
  simpa only [v15213, v15210, v15212, v15211, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 16483) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v15220 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v15220 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 4195) (by decide) matched
  simpa only [v15220, v15217, v15219, v15218, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 4195) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

theorem reference_store_sd_not_v15227 (s : State) (i : Inputs)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 12323) :
    v15227 s i = 0 := by
  have miss := instruction_masks_incompatible (v14575 s i) (BitVec.ofNat 32 28799)
    (BitVec.ofNat 32 12323) (BitVec.ofNat 32 28799) (BitVec.ofNat 32 99) (by decide) matched
  simpa only [v15227, v15224, v15226, v15225, BitVec.and_allOnes] using (show (if (BitVec.ofNat 32 99) = (v14575 s i &&& (BitVec.ofNat 32 28799)) then (1 : BitVec 1) else 0) = 0 by rw [if_neg miss])

end NutShellProofs
