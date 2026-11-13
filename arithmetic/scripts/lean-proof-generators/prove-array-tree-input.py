#!/usr/bin/env python3
"""Connect the actual first-stage register columns to the captured Booth sum.

Each register bit belongs to one physical row. Padding relations identify
inverted and duplicated sign bits. Lean checks column reconstruction, bitwise
row identities, and their algebraic composition; discovery introduces no axioms.
The reconstruction is split into small modules to bound compilation cost.
"""
import pathlib
import re
root = pathlib.Path(__file__).resolve().parents[2] / 'verification'
source = '\n'.join((p.read_text() for p in sorted((root / 'lean/Generated/ArrayMulDataModule').glob('Part*.lean'))))
nodes = {int(n): (int(w), e) for n, w, e in re.findall('def v(\\d+) .*? : BitVec (\\d+) := ([^\\n]+)', source)}
row_source = (root / 'lean/Proofs/ArrayRows.lean').read_text()
rows = list(map(int, re.findall('theorem row_\\d+ .*? : v(\\d+)', row_source)))
corr = list(map(int, re.findall('theorem correction_\\d+ .*? : \\(v(\\d+)', row_source)))
field_row = {}
for node, (width, e) in nodes.items():
    m = re.fullmatch('if i.nio_5FregEnables_5F0 = 1 then \\(v(\\d+) s i\\) else s\\.(g\\d+\\.r\\w+)', e)
    if not m or width != 1:
        continue
    data = int(m[1])
    field = m[2]
    extract = re.fullmatch("BitVec.extractLsb' (\\d+) 1 \\(v(\\d+) s i\\)", nodes[data][1])
    if extract:
        parent = int(extract[2])
        k = rows.index(parent) if parent in rows else corr.index(parent) + 1
    else:
        sign = int(re.fullmatch('\\(\\(v(\\d+) s i\\) \\^\\^\\^ \\(v\\d+ s i\\)\\)', nodes[data][1])[1])
        parent = int(re.fullmatch("BitVec.extractLsb' 65 1 \\(v(\\d+) s i\\)", nodes[sign][1])[1])
        k = rows.index(parent)
    field_row[field] = k
bits = [['(0#1)'] * 130 for _ in range(34)]
boundary = (root / 'lean/Proofs/ArrayTree/Boundary.lean').read_text()
seen = set()
for w in range(130):
    e = re.search(f'def inputColumn{w} .*? := ([^\\n]+)', boundary)[1]
    for field in re.findall('s\\.(g\\d+\\.r\\w+)', e):
        k = field_row[field]
        assert bits[k][w] == '(0#1)' and field not in seen
        bits[k][w] = f'(s.{field})'
        seen.add(field)
    if e.startswith('1 + '):
        k = (w - 67) // 2
        assert w == 2 * k + 67 and 1 <= k <= 31 and (bits[k][w] == '(0#1)')
        bits[k][w] = '(1#1)'
assert seen == set(field_row) and len(seen) == 2278

def sum_text(terms):
    return ' + '.join(terms)

def nat_words(n):
    return sum_text((f'(word{k}_{n} s).toNat' for k in range(34)))
lines = ['import Proofs.ArrayTreeOutput', 'import Proofs.ArrayPaddingRegisters', 'import Proofs.BoothPackedSum', '', 'namespace ArrayTreeInput', 'open nArrayMulDataModule', 'open ArrayTree', 'open ArrayCapture', '', 'set_option maxRecDepth 32768', 'set_option maxHeartbeats 4000000', 'set_option linter.unusedSimpArgs false', '']
binders = ' '.join((f'(a{k} b{k} : Nat)' for k in range(34)))
low = sum_text((f'a{k}' for k in range(34)))
high = sum_text((f'b{k}' for k in range(34)))
new = sum_text((f'(b{k} * weight + a{k})' for k in range(34)))
lines += [f'theorem many_step (weight total : Nat) {binders}', f'    (previous : total = {low}) :', f'    total + weight * ({high}) = {new} := by', '  rw [previous]', '  simp only [Nat.mul_add]', '  ac_rfl', '']
for k in range(34):
    lines += [f'@[noinline] def word{k}_0 (_s : State) : BitVec 0 := 0#0']
lines += ['theorem prefix_0 (s : State) (i : Inputs) :', f'    inputPrefix0 s i = {nat_words(0)} := rfl', '']
for n in range(130):
    for k in range(34):
        lines += [f'@[noinline] def word{k}_{n + 1} (s : State) : BitVec {n + 1} := {bits[k][n]} ++ word{k}_{n} s']
    lines += ['', f'theorem column_{n} (s : State) (i : Inputs) :', f'    inputColumn{n} s i = ' + sum_text((f'{bits[k][n]}.toNat' for k in range(34))) + ' := by', f'  simp only [inputColumn{n}, BitVec.toNat_ofNat, Nat.zero_mod, Nat.one_mod, Nat.add_zero, Nat.zero_add]', '  <;> ac_rfl', '', f'theorem prefix_{n + 1} (s : State) (i : Inputs) :', f'    inputPrefix{n + 1} s i = {nat_words(n + 1)} := by']
    for k in range(34):
        lines += [f'  have h{k} : (word{k}_{n + 1} s).toNat = {bits[k][n]}.toNat * {2 ** n} + (word{k}_{n} s).toNat :=', f'    BitPacking.append_nat {bits[k][n]} (word{k}_{n} s)']
    lines += ['  rw [' + ', '.join([f'inputPrefix{n + 1}'] + [f'h{k}' for k in range(34)] + [f'column_{n}']) + ']', '  exact many_step ' + ' '.join(['_'] * (2 + 68)) + f' (prefix_{n} s i)', '']
lines += ['theorem input_boundary (s : State) (i : Inputs) :', '    BitVec.ofNat 130 (inputPrefix130 s i) = ' + sum_text((f'word{k}_130 s' for k in range(34))) + ' := by', '  have convert ' + ' '.join((f'(a{k} : BitVec 130)' for k in range(34))) + ' :', '      BitVec.ofNat 130 (' + sum_text((f'a{k}.toNat' for k in range(34))) + ') = ' + sum_text((f'a{k}' for k in range(34))) + ' := by', '    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]', '  rw [prefix_130]', '  exact convert ' + ' '.join((f'(word{k}_130 s)' for k in range(34))), '']
capture_source = (root / 'lean/Proofs/ArrayCapture.lean').read_text()
raw_defs = {name: expr for name, expr in re.findall('def (registered_(?:row|correction)_\\d+) .*? := ([^\\n]+)', capture_source)}
pad_source = (root / 'lean/Proofs/ArrayPaddingRegisters.lean').read_text().split('theorem padding_capture_0')[0]
relations = re.findall('s\\.(g\\d+\\.r\\w+) = (~~~)?s\\.(g\\d+\\.r\\w+)', pad_source)
assert len(relations) == 34
row_exprs = []
for k in range(34):
    if k == 0:
        expression = '(BoothRecoding.firstPadded (registered_row_0 s)).zeroExtend 130'
        offset = 0
    elif k < 32:
        expression = f'(BoothRecoding.middlePadded (registered_row_{k} s) (registered_correction_{k - 1} s)).zeroExtend 130'
        offset = 2 * k - 2
    elif k == 32:
        expression = '(BoothRecoding.finalPadded (registered_row_32 s) (registered_correction_31 s)).zeroExtend 130'
        offset = 62
    else:
        expression = '(registered_correction_32 s).zeroExtend 130'
        offset = 64
    row_exprs.append(expression)
    physical = '(0#0)'
    for bit in bits[k]:
        physical = f'({bit} ++ {physical})'
    canonical = physical
    needed = []
    for j, (field, inverted, other) in enumerate(relations):
        if f's.{field}' in canonical:
            canonical = canonical.replace(f's.{field}', ('~~~' if inverted else '') + f's.{other}')
            needed.append(j)
    rhs = f'{2 ** offset}#130 * ({expression})'
    expanded = re.sub('\\((registered_(?:row|correction)_\\d+) s\\)', lambda m: '(' + raw_defs[m[1]] + ')', rhs)
    fields = sorted(set(re.findall('s\\.g\\d+\\.r\\w+', canonical + ' ' + expanded)))
    left, right = (canonical, expanded)
    for j, field in enumerate(fields):
        left = re.sub(re.escape(field) + '(?![A-Za-z0-9_])', f'cut{j}', left)
        right = re.sub(re.escape(field) + '(?![A-Za-z0-9_])', f'cut{j}', right)
    lines += [f'def packed{k} (s : State) : BitVec 130 := {rhs}', '', f'private theorem row_math_{k} ' + ' '.join((f'(cut{j} : BitVec 1)' for j in range(len(fields)))) + ' :', f'    ({left} : BitVec 130) = {right} := by', '  try simp only [BoothRecoding.firstPadded, BoothRecoding.middlePadded, BoothRecoding.finalPadded]', '  bv_decide', '', f'theorem word{k}_packed (s : State) (padding : PaddingInvariant s) :', f'    word{k}_130 s = packed{k} s := by', '  rcases padding with ⟨' + ', '.join([f'h{j}' for j in range(34)] + ['_']) + '⟩', f'  change ({physical} : BitVec 130) = {rhs}']
    if needed:
        lines += ['  rw [' + ', '.join((f'h{j}' for j in needed)) + ']']
    lines += [f'  exact row_math_{k} ' + ' '.join((f'({field})' for field in fields)), '']
base_target = root / 'lean/Proofs/ArrayTreeInput.lean'
base_text = '\n'.join(lines + ['end ArrayTreeInput', ''])
parts = root / 'lean/Proofs/ArrayTreeInput'
parts.mkdir(exist_ok=True)

def write(path, text):
    if not path.exists() or path.read_text() != text:
        path.write_text(text)
header = ['namespace ArrayTreeInput', 'open nArrayMulDataModule', 'open ArrayTree', 'open ArrayCapture', 'set_option maxRecDepth 32768', 'set_option maxHeartbeats 4000000', 'set_option linter.unusedSimpArgs false', '']

def module(imports, body):
    return '\n'.join(imports + [''] + header) + body + '\nend ArrayTreeInput\n'
start = base_text.index('@[noinline] def word0_1 ')
write(parts / 'Base.lean', base_text[:start] + 'end ArrayTreeInput\n')
for batch in range(13):
    begin = base_text.index(f'@[noinline] def word0_{10 * batch + 1} ')
    end = base_text.index(f'@[noinline] def word0_{10 * (batch + 1) + 1} ') if batch < 12 else base_text.index('theorem input_boundary ')
    previous = 'Base' if batch == 0 else f'Part{batch - 1:03}'
    write(parts / f'Part{batch:03}.lean', module([f'import Proofs.ArrayTreeInput.{previous}'], base_text[begin:end]))
for batch in range(5):
    begin = base_text.index(f'def packed{8 * batch} ')
    end = base_text.index(f'def packed{8 * (batch + 1)} ') if batch < 4 else base_text.index('end ArrayTreeInput')
    write(parts / f'Packed{batch:03}.lean', module(['import Proofs.ArrayTreeInput.Part012'], base_text[begin:end]))
begin = base_text.index('theorem input_boundary ')
end = base_text.index('def packed0 ')
write(base_target, module([f'import Proofs.ArrayTreeInput.Packed{batch:03}' for batch in range(5)], base_text[begin:end]))
lines = ['import Proofs.ArrayTreeInput', '', 'namespace ArrayTreeInput', 'open nArrayMulDataModule', 'open ArrayTree', 'open ArrayCapture', 'set_option maxRecDepth 8192', 'set_option maxHeartbeats 2000000', '']
pairs = [f'(registered_row_{k} s, registered_correction_{k} s)' for k in range(33)]
rowlist = '[' + ', '.join(pairs[1:]) + ']'
packed_sum = sum_text((f'packed{k} s' for k in range(34)))
weighted = sum_text((f'{2 ** (0 if k == 0 else 2 * k - 2)}#130 * x{k}' for k in range(34)))
horner = 'x32 + 4#130 * x33'
for k in reversed(range(1, 32)):
    horner = f'x{k} + 4#130 * ({horner})'
horner = 'x0 + (' + horner + ')'
lines += ['private theorem flatten ' + ' '.join((f'(x{k} : BitVec 130)' for k in range(34))) + ' :', f'    {weighted} = {horner} := by', '  simp only [BitVec.mul_add, ← BitVec.mul_assoc, BitVec.one_mul]', '  ac_rfl', '']
lines += ['theorem packed_sum (s : State) :', f'    {packed_sum} = registeredRowSum s := by', f'  have correct := BoothRecoding.packed_sum_65 {pairs[0]} {rowlist} (by rfl)', '  change (BoothRecoding.firstPadded (registered_row_0 s)).zeroExtend 130 +', f'    BoothRecoding.packedTail (registered_correction_0 s) {rowlist} = registeredRowSum s at correct', '  have flat := flatten ' + ' '.join((f'({e})' for e in row_exprs)), f'  change {packed_sum} = (BoothRecoding.firstPadded (registered_row_0 s)).zeroExtend 130 +', f'    BoothRecoding.packedTail (registered_correction_0 s) {rowlist} at flat', '  exact flat.trans correct', '', 'theorem input_equals_rows (s : State) (i : Inputs) (padding : PaddingInvariant s) :', '    BitVec.ofNat 130 (inputPrefix130 s i) = registeredRowSum s := by', '  rw [input_boundary, ' + ', '.join((f'word{k}_packed s padding' for k in range(34))) + ', packed_sum]', '', 'theorem output_from_first_stage (s : State) (i after : Inputs)', '    (enabled : i.nio_5FregEnables_5F1 = 1) (padding : PaddingInvariant s) :', '    (observe (step s i) after).nio_5Fresult = registeredRowSum s := by', '  rw [ArrayTreeOutput.captured_tree_sum s i after enabled, input_equals_rows s i padding]', '', 'end ArrayTreeInput', '']
target = root / 'lean/Proofs/ArrayTreeInputRows.lean'
text = '\n'.join(lines)
if not target.exists() or target.read_text() != text:
    target.write_text(text)
print('Generated input boundary reconstruction: 2278 register bits and 31 constants')
