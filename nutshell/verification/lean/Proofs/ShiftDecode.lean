import Proofs.ImmediateEncoding
import Proofs.DecodeBits
namespace NutShellProofs
open nNutCore
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

inductive ShiftImmediateOp where
  | sll | srl | sra
  deriving DecidableEq

def ShiftImmediateOp.encoding : ShiftImmediateOp → BitVec 64
  | .sll => 4115 | .srl => 20499 | .sra => 1073762323

def ShiftImmediateOp.control : ShiftImmediateOp → BitVec 7
  | .sll => 1 | .srl => 5 | .sra => 13

def IsShiftImmediate (op : ShiftImmediateOp) (instr : BitVec 64) : Prop :=
  instr &&& BitVec.ofNat 64 4227887231 = op.encoding

theorem idu_shift_0_sll_decode (s : State) (i : Inputs)
    (normal : v26384 s i = 0) (matched : IsShiftImmediate .sll (v26210 s i)) :
    v28254 s i = 0 ∧ v28643 s i = 1 ∧ v28010 s i = 0 ∧ v28050 s i = 1 ∧
      v29154 s i = immediateI (v26210 s i) ∧ v28897 s i = 1 := by
  change v26210 s i &&& BitVec.ofNat 64 4227887231 = BitVec.ofNat 64 4115 at matched
  have unitOverride : v28077 s i = 0 := normal
  have opOverride : v28454 s i = 0 := normal
  have hv26389 : v26389 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 4115) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26386, v26388, v26387] using (show v26389 s i = 0 by unfold v26389; exact if_neg miss)
  have hv26394 : v26394 s i = 1 := by
    simp [v26394, v26391, v26393, v26392, matched]
  have format : v26897 s i = 4 := by
    simp [v26897, v26385, v26896, v26895, v26395, normal, unitOverride, opOverride, hv26389, hv26394]
  have unit : v28254 s i = 0 := by
    simp [v28254, v28078, v28253, v28252, v28080, normal, unitOverride, opOverride, hv26389, hv26394, format]
  have operation : v28643 s i = 1 := by
    simp [v28643, v28642, v28641, v28640, v28452, v28451, v28639, v28616, v28615, v28455, v28614, v28613, v28456, v12229, v28638, v28622, v28619, v28617, v28618, v28621, v28620, v8207, v28637, v28628, v28625, v28623, v28624, v28627, v28626, v8322, v28636, v28635, v28633, v28630, v28629, v28632, v28631, v28634, v12225, normal, unitOverride, opOverride, hv26389, hv26394, format, unit]
  have kind1 : v28010 s i = 0 := by
    simp [v28010, v28009, v28008, v28007, v27998, v27996, v27997, v24, v28006, v28003, v28000, v27999, v28002, v28001, v28005, v28004, normal, unitOverride, opOverride, hv26389, hv26394, format, unit, operation]
  have kind2 : v28050 s i = 1 := by
    simp [v28050, v28049, v28048, v28047, v28044, v28041, v28038, v28037, v28040, v28039, v28043, v28042, v28046, v28045, normal, unitOverride, opOverride, hv26389, hv26394, format, unit, operation, kind1]
  have write : v28897 s i = 1 := by
    simp [v28897, v28896, v28895, v28894, normal, unitOverride, opOverride, hv26389, hv26394, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_0_i s i format, write⟩
#print axioms idu_shift_0_sll_decode

theorem idu_shift_0_srl_decode (s : State) (i : Inputs)
    (normal : v26384 s i = 0) (matched : IsShiftImmediate .srl (v26210 s i)) :
    v28254 s i = 0 ∧ v28643 s i = 5 ∧ v28010 s i = 0 ∧ v28050 s i = 1 ∧
      v29154 s i = immediateI (v26210 s i) ∧ v28897 s i = 1 := by
  change v26210 s i &&& BitVec.ofNat 64 4227887231 = BitVec.ofNat 64 20499 at matched
  have unitOverride : v28077 s i = 0 := normal
  have opOverride : v28454 s i = 0 := normal
  have hv26389 : v26389 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 20499) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26386, v26388, v26387] using (show v26389 s i = 0 by unfold v26389; exact if_neg miss)
  have hv26394 : v26394 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 20499) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26391, v26393, v26392] using (show v26394 s i = 0 by unfold v26394; exact if_neg miss)
  have hv26399 : v26399 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 20499) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26396, v26398, v26397] using (show v26399 s i = 0 by unfold v26399; exact if_neg miss)
  have hv26404 : v26404 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 20499) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26401, v26403, v26402] using (show v26404 s i = 0 by unfold v26404; exact if_neg miss)
  have hv26409 : v26409 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 20499) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26406, v26408, v26407] using (show v26409 s i = 0 by unfold v26409; exact if_neg miss)
  have hv26414 : v26414 s i = 1 := by
    simp [v26414, v26411, v26413, v26412, matched]
  have format : v26897 s i = 4 := by
    simp [v26897, v26385, v26896, v26895, v26894, v26893, v26892, v26891, v26415, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414]
  have unit : v28254 s i = 0 := by
    simp [v28254, v28078, v28253, v28252, v28251, v28250, v28249, v28248, v28084, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, format]
  have operation : v28643 s i = 5 := by
    simp [v28643, v28642, v28641, v28640, v28452, v28451, v28639, v28616, v28615, v28455, v28614, v28613, v28612, v28611, v28610, v28609, v28460, v12229, v28638, v28622, v28619, v28617, v28618, v28621, v28620, v8207, v28637, v28628, v28625, v28623, v28624, v28627, v28626, v8322, v28636, v28635, v28633, v28630, v28629, v28632, v28631, v28634, v12225, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, format, unit]
  have kind1 : v28010 s i = 0 := by
    simp [v28010, v28009, v28008, v28007, v27998, v27996, v27997, v24, v28006, v28003, v28000, v27999, v28002, v28001, v28005, v28004, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, format, unit, operation]
  have kind2 : v28050 s i = 1 := by
    simp [v28050, v28049, v28048, v28047, v28044, v28041, v28038, v28037, v28040, v28039, v28043, v28042, v28046, v28045, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, format, unit, operation, kind1]
  have write : v28897 s i = 1 := by
    simp [v28897, v28896, v28895, v28894, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_0_i s i format, write⟩
#print axioms idu_shift_0_srl_decode

theorem idu_shift_0_sra_decode (s : State) (i : Inputs)
    (normal : v26384 s i = 0) (matched : IsShiftImmediate .sra (v26210 s i)) :
    v28254 s i = 0 ∧ v28643 s i = 13 ∧ v28010 s i = 0 ∧ v28050 s i = 1 ∧
      v29154 s i = immediateI (v26210 s i) ∧ v28897 s i = 1 := by
  change v26210 s i &&& BitVec.ofNat 64 4227887231 = BitVec.ofNat 64 1073762323 at matched
  have unitOverride : v28077 s i = 0 := normal
  have opOverride : v28454 s i = 0 := normal
  have hv26389 : v26389 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 1073762323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26386, v26388, v26387] using (show v26389 s i = 0 by unfold v26389; exact if_neg miss)
  have hv26394 : v26394 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 1073762323) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26391, v26393, v26392] using (show v26394 s i = 0 by unfold v26394; exact if_neg miss)
  have hv26399 : v26399 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 1073762323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26396, v26398, v26397] using (show v26399 s i = 0 by unfold v26399; exact if_neg miss)
  have hv26404 : v26404 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 1073762323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26401, v26403, v26402] using (show v26404 s i = 0 by unfold v26404; exact if_neg miss)
  have hv26409 : v26409 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 1073762323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26406, v26408, v26407] using (show v26409 s i = 0 by unfold v26409; exact if_neg miss)
  have hv26414 : v26414 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 1073762323) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26411, v26413, v26412] using (show v26414 s i = 0 by unfold v26414; exact if_neg miss)
  have hv26419 : v26419 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 1073762323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26416, v26418, v26417] using (show v26419 s i = 0 by unfold v26419; exact if_neg miss)
  have hv26424 : v26424 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 1073762323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26421, v26423, v26422] using (show v26424 s i = 0 by unfold v26424; exact if_neg miss)
  have hv26429 : v26429 s i = 1 := by
    simp [v26429, v26426, v26428, v26427, matched]
  have format : v26897 s i = 4 := by
    simp [v26897, v26385, v26896, v26895, v26894, v26893, v26892, v26891, v26890, v26889, v26888, v26430, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429]
  have unit : v28254 s i = 0 := by
    simp [v28254, v28078, v28253, v28252, v28251, v28250, v28249, v28248, v28247, v28246, v28245, v28087, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, format]
  have operation : v28643 s i = 13 := by
    simp [v28643, v28642, v28641, v28640, v28452, v28451, v28639, v28616, v28615, v28455, v28614, v28613, v28612, v28611, v28610, v28609, v28608, v28607, v28606, v28463, v12229, v28638, v28622, v28619, v28617, v28618, v28621, v28620, v8207, v28637, v28628, v28625, v28623, v28624, v28627, v28626, v8322, v28636, v28635, v28633, v28630, v28629, v28632, v28631, v28634, v12225, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, format, unit]
  have kind1 : v28010 s i = 0 := by
    simp [v28010, v28009, v28008, v28007, v27998, v27996, v27997, v24, v28006, v28003, v28000, v27999, v28002, v28001, v28005, v28004, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, format, unit, operation]
  have kind2 : v28050 s i = 1 := by
    simp [v28050, v28049, v28048, v28047, v28044, v28041, v28038, v28037, v28040, v28039, v28043, v28042, v28046, v28045, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, format, unit, operation, kind1]
  have write : v28897 s i = 1 := by
    simp [v28897, v28896, v28895, v28894, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_0_i s i format, write⟩
#print axioms idu_shift_0_sra_decode

theorem idu_shift_1_sll_decode (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (matched : IsShiftImmediate .sll (v26223 s i)) :
    v28438 s i = 0 ∧ v28836 s i = 1 ∧ v28027 s i = 0 ∧ v28066 s i = 1 ∧
      v29230 s i = immediateI (v26223 s i) ∧ v28903 s i = 1 := by
  change v26223 s i &&& BitVec.ofNat 64 4227887231 = BitVec.ofNat 64 4115 at matched
  have unitOverride : v28261 s i = 0 := normal
  have opOverride : v28649 s i = 0 := normal
  have hv26916 : v26916 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 4115) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26913, v26915, v26914] using (show v26916 s i = 0 by unfold v26916; exact if_neg miss)
  have hv26921 : v26921 s i = 1 := by
    simp [v26921, v26918, v26920, v26919, matched]
  have format : v27424 s i = 4 := by
    simp [v27424, v26912, v27423, v27422, v26922, normal, unitOverride, opOverride, hv26916, hv26921]
  have unit : v28438 s i = 0 := by
    simp [v28438, v28262, v28437, v28436, v28264, normal, unitOverride, opOverride, hv26916, hv26921, format]
  have operation : v28836 s i = 1 := by
    simp [v28836, v28835, v28834, v28833, v28647, v28646, v28832, v28809, v28808, v28650, v28807, v28806, v28651, v12229, v28831, v28815, v28812, v28810, v28811, v28814, v28813, v8207, v28830, v28821, v28818, v28816, v28817, v28820, v28819, v8322, v28829, v28828, v28826, v28823, v28822, v28825, v28824, v28827, v12225, normal, unitOverride, opOverride, hv26916, hv26921, format, unit]
  have kind1 : v28027 s i = 0 := by
    simp [v28027, v28026, v28025, v28024, v28015, v28013, v28014, v24, v28023, v28020, v28017, v28016, v28019, v28018, v28022, v28021, normal, unitOverride, opOverride, hv26916, hv26921, format, unit, operation]
  have kind2 : v28066 s i = 1 := by
    simp [v28066, v28065, v28064, v28063, v28060, v28057, v28054, v28053, v28056, v28055, v28059, v28058, v28062, v28061, normal, unitOverride, opOverride, hv26916, hv26921, format, unit, operation, kind1]
  have write : v28903 s i = 1 := by
    simp [v28903, v28902, v28901, v28900, normal, unitOverride, opOverride, hv26916, hv26921, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_1_i s i format, write⟩
#print axioms idu_shift_1_sll_decode

theorem idu_shift_1_srl_decode (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (matched : IsShiftImmediate .srl (v26223 s i)) :
    v28438 s i = 0 ∧ v28836 s i = 5 ∧ v28027 s i = 0 ∧ v28066 s i = 1 ∧
      v29230 s i = immediateI (v26223 s i) ∧ v28903 s i = 1 := by
  change v26223 s i &&& BitVec.ofNat 64 4227887231 = BitVec.ofNat 64 20499 at matched
  have unitOverride : v28261 s i = 0 := normal
  have opOverride : v28649 s i = 0 := normal
  have hv26916 : v26916 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 20499) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26913, v26915, v26914] using (show v26916 s i = 0 by unfold v26916; exact if_neg miss)
  have hv26921 : v26921 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 20499) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26918, v26920, v26919] using (show v26921 s i = 0 by unfold v26921; exact if_neg miss)
  have hv26926 : v26926 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 20499) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26923, v26925, v26924] using (show v26926 s i = 0 by unfold v26926; exact if_neg miss)
  have hv26931 : v26931 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 20499) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26928, v26930, v26929] using (show v26931 s i = 0 by unfold v26931; exact if_neg miss)
  have hv26936 : v26936 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 20499) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26933, v26935, v26934] using (show v26936 s i = 0 by unfold v26936; exact if_neg miss)
  have hv26941 : v26941 s i = 1 := by
    simp [v26941, v26938, v26940, v26939, matched]
  have format : v27424 s i = 4 := by
    simp [v27424, v26912, v27423, v27422, v27421, v27420, v27419, v27418, v26942, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941]
  have unit : v28438 s i = 0 := by
    simp [v28438, v28262, v28437, v28436, v28435, v28434, v28433, v28432, v28268, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, format]
  have operation : v28836 s i = 5 := by
    simp [v28836, v28835, v28834, v28833, v28647, v28646, v28832, v28809, v28808, v28650, v28807, v28806, v28805, v28804, v28803, v28802, v28655, v12229, v28831, v28815, v28812, v28810, v28811, v28814, v28813, v8207, v28830, v28821, v28818, v28816, v28817, v28820, v28819, v8322, v28829, v28828, v28826, v28823, v28822, v28825, v28824, v28827, v12225, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, format, unit]
  have kind1 : v28027 s i = 0 := by
    simp [v28027, v28026, v28025, v28024, v28015, v28013, v28014, v24, v28023, v28020, v28017, v28016, v28019, v28018, v28022, v28021, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, format, unit, operation]
  have kind2 : v28066 s i = 1 := by
    simp [v28066, v28065, v28064, v28063, v28060, v28057, v28054, v28053, v28056, v28055, v28059, v28058, v28062, v28061, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, format, unit, operation, kind1]
  have write : v28903 s i = 1 := by
    simp [v28903, v28902, v28901, v28900, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_1_i s i format, write⟩
#print axioms idu_shift_1_srl_decode

theorem idu_shift_1_sra_decode (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (matched : IsShiftImmediate .sra (v26223 s i)) :
    v28438 s i = 0 ∧ v28836 s i = 13 ∧ v28027 s i = 0 ∧ v28066 s i = 1 ∧
      v29230 s i = immediateI (v26223 s i) ∧ v28903 s i = 1 := by
  change v26223 s i &&& BitVec.ofNat 64 4227887231 = BitVec.ofNat 64 1073762323 at matched
  have unitOverride : v28261 s i = 0 := normal
  have opOverride : v28649 s i = 0 := normal
  have hv26916 : v26916 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 1073762323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26913, v26915, v26914] using (show v26916 s i = 0 by unfold v26916; exact if_neg miss)
  have hv26921 : v26921 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 1073762323) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26918, v26920, v26919] using (show v26921 s i = 0 by unfold v26921; exact if_neg miss)
  have hv26926 : v26926 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 1073762323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26923, v26925, v26924] using (show v26926 s i = 0 by unfold v26926; exact if_neg miss)
  have hv26931 : v26931 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 1073762323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26928, v26930, v26929] using (show v26931 s i = 0 by unfold v26931; exact if_neg miss)
  have hv26936 : v26936 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 1073762323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26933, v26935, v26934] using (show v26936 s i = 0 by unfold v26936; exact if_neg miss)
  have hv26941 : v26941 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 1073762323) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26938, v26940, v26939] using (show v26941 s i = 0 by unfold v26941; exact if_neg miss)
  have hv26946 : v26946 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 1073762323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26943, v26945, v26944] using (show v26946 s i = 0 by unfold v26946; exact if_neg miss)
  have hv26951 : v26951 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 1073762323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26948, v26950, v26949] using (show v26951 s i = 0 by unfold v26951; exact if_neg miss)
  have hv26956 : v26956 s i = 1 := by
    simp [v26956, v26953, v26955, v26954, matched]
  have format : v27424 s i = 4 := by
    simp [v27424, v26912, v27423, v27422, v27421, v27420, v27419, v27418, v27417, v27416, v27415, v26957, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956]
  have unit : v28438 s i = 0 := by
    simp [v28438, v28262, v28437, v28436, v28435, v28434, v28433, v28432, v28431, v28430, v28429, v28271, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, format]
  have operation : v28836 s i = 13 := by
    simp [v28836, v28835, v28834, v28833, v28647, v28646, v28832, v28809, v28808, v28650, v28807, v28806, v28805, v28804, v28803, v28802, v28801, v28800, v28799, v28658, v12229, v28831, v28815, v28812, v28810, v28811, v28814, v28813, v8207, v28830, v28821, v28818, v28816, v28817, v28820, v28819, v8322, v28829, v28828, v28826, v28823, v28822, v28825, v28824, v28827, v12225, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, format, unit]
  have kind1 : v28027 s i = 0 := by
    simp [v28027, v28026, v28025, v28024, v28015, v28013, v28014, v24, v28023, v28020, v28017, v28016, v28019, v28018, v28022, v28021, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, format, unit, operation]
  have kind2 : v28066 s i = 1 := by
    simp [v28066, v28065, v28064, v28063, v28060, v28057, v28054, v28053, v28056, v28055, v28059, v28058, v28062, v28061, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, format, unit, operation, kind1]
  have write : v28903 s i = 1 := by
    simp [v28903, v28902, v28901, v28900, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_1_i s i format, write⟩
#print axioms idu_shift_1_sra_decode

end NutShellProofs
