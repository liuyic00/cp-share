import Proofs.ImmediateEncoding
import Proofs.DecodeBits
namespace NutShellProofs
open nNutCore
/-- Standard ADDI opcode/funct3 match; upper instruction bits are irrelevant. -/
def IsADDI (instr : BitVec 64) : Prop :=
  instr &&& BitVec.ofNat 64 28799 = BitVec.ofNat 64 19

theorem idu_addi_0_match (s : State) (i : Inputs) (addi : IsADDI (v26210 s i)) :
    v26389 s i = 1 := by
  unfold IsADDI at addi
  simp [v26389, v26386, v26388, v26387, addi]

theorem idu_addi_0_format (s : State) (i : Inputs) (normal : v26384 s i = 0) (addi : IsADDI (v26210 s i)) :
    v26897 s i = 4 := by
  have matched := idu_addi_0_match s i addi
  simp [v26897, v26385, v26896, v26390, normal, matched]

theorem idu_addi_0_unit (s : State) (i : Inputs) (normal : v26384 s i = 0) (addi : IsADDI (v26210 s i)) :
    v28254 s i = 0 := by
  have override : v28077 s i = 0 := normal
  have matched := idu_addi_0_match s i addi
  simp [v28254, v28078, v28253, v28079, override, matched]

theorem idu_addi_0_operation (s : State) (i : Inputs) (normal : v26384 s i = 0) (addi : IsADDI (v26210 s i)) :
    v28643 s i = 64 := by
  have override : v28454 s i = 0 := normal
  have matched := idu_addi_0_match s i addi
  have unit := idu_addi_0_unit s i normal addi
  simp [v28643, v28642, v28641, v28640, v28452, v28451, v28639, v28616, v28615, v28455, v28614, v12968, v12229, v28638, v28622, v28619, v28617, v28618, v28621, v28620, v8207, v28637, v28628, v28625, v28623, v28624, v28627, v28626, v8322, v28636, v28635, v28633, v28630, v28629, v28632, v28631, v28634, v12225, override, matched, unit]

theorem idu_addi_0_source1 (s : State) (i : Inputs) (normal : v26384 s i = 0) (addi : IsADDI (v26210 s i)) :
    v28010 s i = 0 := by
  have format := idu_addi_0_format s i normal addi
  simp [v28010, v28009, v28008, v28007, v27998, v27996, v27997, v24, v28006, v28003, v28000, v27999, v28002, v28001, v28005, v28004, format]

theorem idu_addi_0_source2 (s : State) (i : Inputs) (normal : v26384 s i = 0) (addi : IsADDI (v26210 s i)) :
    v28050 s i = 1 := by
  have format := idu_addi_0_format s i normal addi
  simp [v28050, v28049, v28048, v28047, v28044, v28041, v28038, v28037, v28040, v28039, v28043, v28042, v28046, v28045, format]

theorem idu_addi_0_immediate (s : State) (i : Inputs) (normal : v26384 s i = 0) (addi : IsADDI (v26210 s i)) :
    v29154 s i = immediateI (v26210 s i) :=
  idu_immediate_0_i s i (idu_addi_0_format s i normal addi)

theorem idu_addi_0_write (s : State) (i : Inputs) (normal : v26384 s i = 0) (addi : IsADDI (v26210 s i)) :
    v28897 s i = 1 := by
  have format := idu_addi_0_format s i normal addi
  simp [v28897, v28896, v28895, v28894, format]

#print axioms idu_addi_0_format
#print axioms idu_addi_0_unit
#print axioms idu_addi_0_operation
#print axioms idu_addi_0_source1
#print axioms idu_addi_0_source2
#print axioms idu_addi_0_immediate
theorem idu_addi_1_match (s : State) (i : Inputs) (addi : IsADDI (v26223 s i)) :
    v26916 s i = 1 := by
  unfold IsADDI at addi
  simp [v26916, v26913, v26915, v26914, addi]

theorem idu_addi_1_format (s : State) (i : Inputs) (normal : v26911 s i = 0) (addi : IsADDI (v26223 s i)) :
    v27424 s i = 4 := by
  have matched := idu_addi_1_match s i addi
  simp [v27424, v26912, v27423, v26917, normal, matched]

theorem idu_addi_1_unit (s : State) (i : Inputs) (normal : v26911 s i = 0) (addi : IsADDI (v26223 s i)) :
    v28438 s i = 0 := by
  have override : v28261 s i = 0 := normal
  have matched := idu_addi_1_match s i addi
  simp [v28438, v28262, v28437, v28263, override, matched]

theorem idu_addi_1_operation (s : State) (i : Inputs) (normal : v26911 s i = 0) (addi : IsADDI (v26223 s i)) :
    v28836 s i = 64 := by
  have override : v28649 s i = 0 := normal
  have matched := idu_addi_1_match s i addi
  have unit := idu_addi_1_unit s i normal addi
  simp [v28836, v28835, v28834, v28833, v28647, v28646, v28832, v28809, v28808, v28650, v28807, v12968, v12229, v28831, v28815, v28812, v28810, v28811, v28814, v28813, v8207, v28830, v28821, v28818, v28816, v28817, v28820, v28819, v8322, v28829, v28828, v28826, v28823, v28822, v28825, v28824, v28827, v12225, override, matched, unit]

theorem idu_addi_1_source1 (s : State) (i : Inputs) (normal : v26911 s i = 0) (addi : IsADDI (v26223 s i)) :
    v28027 s i = 0 := by
  have format := idu_addi_1_format s i normal addi
  simp [v28027, v28026, v28025, v28024, v28015, v28013, v28014, v24, v28023, v28020, v28017, v28016, v28019, v28018, v28022, v28021, format]

theorem idu_addi_1_source2 (s : State) (i : Inputs) (normal : v26911 s i = 0) (addi : IsADDI (v26223 s i)) :
    v28066 s i = 1 := by
  have format := idu_addi_1_format s i normal addi
  simp [v28066, v28065, v28064, v28063, v28060, v28057, v28054, v28053, v28056, v28055, v28059, v28058, v28062, v28061, format]

theorem idu_addi_1_immediate (s : State) (i : Inputs) (normal : v26911 s i = 0) (addi : IsADDI (v26223 s i)) :
    v29230 s i = immediateI (v26223 s i) :=
  idu_immediate_1_i s i (idu_addi_1_format s i normal addi)

theorem idu_addi_1_write (s : State) (i : Inputs) (normal : v26911 s i = 0) (addi : IsADDI (v26223 s i)) :
    v28903 s i = 1 := by
  have format := idu_addi_1_format s i normal addi
  simp [v28903, v28902, v28901, v28900, format]

#print axioms idu_addi_1_format
#print axioms idu_addi_1_unit
#print axioms idu_addi_1_operation
#print axioms idu_addi_1_source1
#print axioms idu_addi_1_source2
#print axioms idu_addi_1_immediate
end NutShellProofs
