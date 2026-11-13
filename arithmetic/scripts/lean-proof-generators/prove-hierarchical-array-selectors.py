#!/usr/bin/env python3
"""Prove each generated ArrayMul selector against the shared Booth contract."""
from pathlib import Path
import re
root = Path(__file__).resolve().parents[2] / 'verification' / 'lean-hierarchical'
text = '\n'.join(p.read_text() for p in sorted((root/'Generated/ArrayMulDataModule').glob('Part*.lean')))
text = text[text.index('namespace nArrayMulDataModule'):]
nodes = {name: (int(width), body) for name, width, body in re.findall(
    r'def (v\d+) \(s : State\) \(i : Inputs\) : BitVec (\d+) := ([^\n]+)', text)}
def closure(name):
    seen = set()
    def visit(n):
        if n in seen: return
        seen.add(n)
        for dep in re.findall(r'\b(v\d+) s i', nodes[n][1]): visit(dep)
    visit(name)
    return seen
raws = ['v13'] + [n for n, (w, b) in nodes.items() if w == 66 and re.fullmatch(r'if \(v\d+ s i\) = 1 then \(v38 s i\) else \(v\d+ s i\)', b)]
assert len(raws) == 33, len(raws)
lines = ['import Generated.ArrayMulDataModule.Part006', 'import Proofs.BoothSelector', '',
         'namespace HierarchicalArray', 'open DesignnArrayMulDataModule.nArrayMulDataModule',
         'open HierarchicalBooth', '']
for index, raw in enumerate(raws):
    deps = closure(raw)
    if index == 0:
        code = "(BitVec.extractLsb' 0 2 i.nio_5Fa ++ 0#1)"
        correction = 'v23'
    else:
        candidates = [n for n in deps if nodes[n][0] == 3 and 'BitVec.ofNat' not in nodes[n][1]]
        assert len(candidates) == 1, candidates
        code = f'({candidates[0]} s i)'
        cond = re.match(r'if \((v\d+) s i\)', nodes[raw][1])[1]
        corrections = [n for n, (w, b) in nodes.items() if w == 2 and b.startswith(f'if ({cond} s i) = 1 then (v19 s i)')]
        assert len(corrections) == 1
        correction = corrections[0]
    for suffix, node, rhs in [('raw', raw, f'rawPartial {code} (i.nio_5Fb.signExtend 66)'),
                              ('correction', correction, f'correction {code}')]:
        lhs = f'{node} s i' if suffix == 'raw' else f'({node} s i).setWidth 66'
        defs = ', '.join(sorted(closure(node), key=lambda n: int(n[1:])))
        lines += [f'theorem selector_{index}_{suffix} (s : State) (i : Inputs) :',
                  f'    {lhs} = {rhs} := by',
                  f'  simp only [{defs}, rawPartial, correction]', '  bv_decide', '']
lines += ['end HierarchicalArray', '']
(root/'Proofs/ArraySelectors.lean').write_text('\n'.join(lines))
print(f'Generated raw-row and correction contracts for {len(raws)} selectors')

lines = ['import Generated.ArrayMulDataModule.Part006', 'import Proofs.BoothSelector', '',
         'namespace HierarchicalArray', 'open DesignnArrayMulDataModule.nArrayMulDataModule',
         'open HierarchicalBooth', '']
for index, raw in enumerate(raws):
    if index == 0:
        code = "(BitVec.extractLsb' 0 2 i.nio_5Fa ++ 0#1)"
        defs = []
    else:
        name, = [n for n in closure(raw) if nodes[n][0] == 3 and 'BitVec.ofNat' not in nodes[n][1]]
        code = f'({name} s i)'
        defs = sorted(closure(name), key=lambda n: int(n[1:]))
    lines += [f'theorem selector_{index}_code (s : State) (i : Inputs) :',
              f'    {code} = operandCode i.nio_5Fa.toInt {index} := by']
    if defs: lines += ['  simp only [' + ', '.join(defs) + ']']
    lines += ['  apply BitVec.eq_of_toNat_eq']
    if index == 0: lines += ['  rw [BitVec.toNat_append]']
    if index == 32:
        lines += ["  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (BitVec.extractLsb' 63 2 i.nio_5Fa).isLt]"]
    lines += ['  have bound := i.nio_5Fa.isLt',
              '  simp [operandCode, chunk, quotient, overlap, BitVec.toInt_eq_toNat_cond,',
              '    Nat.shiftRight_eq_div_pow' + (', Nat.shiftLeft_eq]' if index in (0, 32) else ']'),
              '  split <;> omega', '']
lines += ['end HierarchicalArray', '']
(root/'Proofs/ArrayCodes.lean').write_text('\n'.join(lines))

lines = ['import Proofs.ArraySelectors', 'import Proofs.ArrayCodes', '',
         'namespace HierarchicalArray', 'open DesignnArrayMulDataModule.nArrayMulDataModule',
         'open HierarchicalBooth', '']
for index, raw in enumerate(raws):
    if index == 0:
        correction = 'v23'
    else:
        cond = re.match(r'if \((v\d+) s i\)', nodes[raw][1])[1]
        correction, = [n for n, (w, b) in nodes.items() if w == 2 and b.startswith(f'if ({cond} s i) = 1 then (v19 s i)')]
    lines += [f'theorem partial_product_{index} (s : State) (i : Inputs) :',
              f'    {raw} s i + ({correction} s i).setWidth 66 =',
              f'      BitVec.ofInt 66 (digit i.nio_5Fa.toInt {index} * i.nio_5Fb.toInt) := by',
              f'  rw [selector_{index}_raw, selector_{index}_correction, (selector_{index}_code s i),',
              '    corrected_signed_partial, operand_coefficient]', '']
lines += ['end HierarchicalArray', '']
(root/'Proofs/ArrayPartialProducts.lean').write_text('\n'.join(lines))

lines = ['import Proofs.ArraySelectors', 'import Proofs.ArrayCodes', 'import Proofs.BoothWidePartial', '',
         'namespace HierarchicalArray', 'open DesignnArrayMulDataModule.nArrayMulDataModule',
         'open HierarchicalBooth', '',
         'private theorem widen_correction (x : BitVec 2) :',
         '    (x.setWidth 66).setWidth 130 = x.setWidth 130 := by bv_decide', '']
for index, raw in enumerate(raws):
    if index == 0:
        correction = 'v23'
    else:
        cond = re.match(r'if \((v\d+) s i\)', nodes[raw][1])[1]
        correction, = [n for n, (w, b) in nodes.items() if w == 2 and b.startswith(f'if ({cond} s i) = 1 then (v19 s i)')]
    lines += [f'theorem wide_partial_product_{index} (s : State) (i : Inputs) :',
              f'    ({raw} s i).signExtend 130 + ({correction} s i).setWidth 130 =',
              f'      BitVec.ofInt 130 (digit i.nio_5Fa.toInt {index} * i.nio_5Fb.toInt) := by',
              f'  rw [← widen_correction, selector_{index}_raw, selector_{index}_correction,',
              f'    (selector_{index}_code s i), corrected_wide_partial, operand_coefficient]', '']
lines += ['end HierarchicalArray', '']
(root/'Proofs/ArrayWidePartialProducts.lean').write_text('\n'.join(lines))

lines = ['import Proofs.ArrayWidePartialProducts', 'import Proofs.BoothBitVecSum', '',
         'namespace HierarchicalArray', 'open DesignnArrayMulDataModule.nArrayMulDataModule',
         'open HierarchicalBooth', '',
         'def correctedRow (s : State) (i : Inputs) : Nat → BitVec 130']
for index, raw in enumerate(raws):
    if index == 0:
        correction = 'v23'
    else:
        cond = re.match(r'if \((v\d+) s i\)', nodes[raw][1])[1]
        correction, = [n for n, (w, b) in nodes.items() if w == 2 and b.startswith(f'if ({cond} s i) = 1 then (v19 s i)')]
    lines += [f'  | {index} => ({raw} s i).signExtend 130 + ({correction} s i).setWidth 130']
lines += ['  | _ => 0', '',
          '/-- The actual selector rows, with their own correction bits restored,',
          '    have the required signed product as their radix-four weighted sum. -/',
          'theorem corrected_rows_product (s : State) (i : Inputs) :',
          '    weightedBits 33 (correctedRow s i) =',
          '      BitVec.ofInt 130 (i.nio_5Fa.toInt * i.nio_5Fb.toInt) := by',
          '  have rows : weightedBits 33 (correctedRow s i) =',
          '      weightedBits 33 (fun k => BitVec.ofInt 130 (digit i.nio_5Fa.toInt k * i.nio_5Fb.toInt)) := by',
          '    simp only [weightedBits, correctedRow, ' + ', '.join(f'wide_partial_product_{k}' for k in range(33)) + ']',
          '  rw [rows, weightedBits_ofInt, operand_product_65]', '', 'end HierarchicalArray', '']
(root/'Proofs/ArrayRowArithmetic.lean').write_text('\n'.join(lines))

lines = ['import Proofs.ArrayRowArithmetic', 'import Proofs.BoothPackedSum', '',
         'namespace HierarchicalArray', 'open DesignnArrayMulDataModule.nArrayMulDataModule',
         'open HierarchicalBooth', '', 'def rawRow (s : State) (i : Inputs) : Nat → BitVec 66']
lines += [f'  | {index} => {raw} s i' for index, raw in enumerate(raws)]
lines += ['  | _ => 0', '', 'def rowCorrection (s : State) (i : Inputs) : Nat → BitVec 2']
for index, raw in enumerate(raws):
    if index == 0:
        correction = 'v23'
    else:
        cond = re.match(r'if \((v\d+) s i\)', nodes[raw][1])[1]
        correction, = [n for n, (w, b) in nodes.items() if w == 2 and b.startswith(f'if ({cond} s i) = 1 then (v19 s i)')]
    lines += [f'  | {index} => {correction} s i']
lines += ['  | _ => 0', '',
          'def packedInputSum (s : State) (i : Inputs) : BitVec 130 :=',
          '  firstPacked (rawRow s i 0) +',
          '    weightedBits 32 (fun k => nextPacked (decide (k = 31)) (rawRow s i (k + 1)) (rowCorrection s i k)) +',
          '    BitVec.ofNat 130 (4^32) * (rowCorrection s i 32).setWidth 130', '',
          '/-- The packed input rows include the actual selector values, the',
          '    correction from the preceding row, and the final correction. -/',
          'theorem packed_input_product (s : State) (i : Inputs) :',
          '    packedInputSum s i = BitVec.ofInt 130 (i.nio_5Fa.toInt * i.nio_5Fb.toInt) := by',
          '  unfold packedInputSum',
          '  rw [packed_sum]',
          '  have rows : weightedBits 33 (fun k => (rawRow s i k).signExtend 130 +',
          '      (rowCorrection s i k).setWidth 130) = weightedBits 33 (correctedRow s i) := by',
          '    simp only [weightedBits, rawRow, rowCorrection, correctedRow]',
          '  rw [rows, corrected_rows_product]', '', 'end HierarchicalArray', '']
(root/'Proofs/ArrayPackedInput.lean').write_text('\n'.join(lines))
