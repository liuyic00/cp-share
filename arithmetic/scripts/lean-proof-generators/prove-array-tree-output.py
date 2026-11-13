#!/usr/bin/env python3
"""Connect the tree's weighted output boundary to the actual captured words."""
import pathlib
import re

root = pathlib.Path(__file__).resolve().parents[2] / 'verification'
source = (root / 'lean/Proofs/ArrayOutput.lean').read_text()
bits = []
for k in range(3):
    expr = re.search(rf'def incomingRow{k} .*? :=\n  ([^\n]+)', source)[1]
    row = list(reversed(re.findall(r'\(v\d+ s i\)|\(0#1\)', expr)))
    assert len(row) == 130
    bits.append(row)
lines = ['import Proofs.ArrayTree', 'import Proofs.ArrayOutput', 'import Proofs.BitPacking', '',
         'namespace ArrayTreeOutput', 'open nArrayMulDataModule', 'open ArrayTree', '',
         'set_option maxRecDepth 8192', 'set_option maxHeartbeats 2000000', 'set_option linter.unusedSimpArgs false', '']
for k in range(3):
    lines += [f'def word{k}_0 (_s : State) (_i : Inputs) : BitVec 0 := 0#0']
lines += ['theorem prefix_0 (s : State) (i : Inputs) :',
          '    outputPrefix0 s i = (word0_0 s i).toNat + (word1_0 s i).toNat + (word2_0 s i).toNat := rfl', '']
for n in range(130):
    for k in range(3):
        lines += [f'def word{k}_{n+1} (s : State) (i : Inputs) : BitVec {n+1} :=',
                  f'  {bits[k][n]} ++ word{k}_{n} s i', '']
    lines += [f'theorem column_{n} (s : State) (i : Inputs) :',
              f'    outputColumn{n} s i = ' + ' + '.join(f'{bits[k][n]}.toNat' for k in range(3)) + ' := by',
              f'  simp only [outputColumn{n}, BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero, Nat.zero_add]',
              '  <;> ac_rfl', '',
              f'theorem prefix_{n+1} (s : State) (i : Inputs) :',
              f'    outputPrefix{n+1} s i = ' + ' + '.join(f'(word{k}_{n+1} s i).toNat' for k in range(3)) + ' := by']
    for k in range(3):
        lines += [f'  have h{k} : (word{k}_{n+1} s i).toNat = {bits[k][n]}.toNat * {2**n} + (word{k}_{n} s i).toNat :=',
                  f'    BitPacking.append_nat {bits[k][n]} (word{k}_{n} s i)']
    lines += [f'  rw [outputPrefix{n+1}, h0, h1, h2, column_{n}]',
              '  exact BitPacking.three_step _ _ _ _ _ _ _ _ (prefix_' + str(n) + ' s i)', '']
for k in range(3):
    lines += [f'theorem word{k}_full (s : State) (i : Inputs) :',
              f'    word{k}_130 s i = ArrayOutput.incomingRow{k} s i := by',
              '  simp only [' + ', '.join([f'ArrayOutput.incomingRow{k}'] + [f'word{k}_{n}' for n in reversed(range(131))]) + ']',
              '  bv_decide', '']
lines += ['theorem output_boundary (s : State) (i : Inputs) :',
          '    outputPrefix130 s i = (ArrayOutput.incomingRow0 s i).toNat +',
          '      (ArrayOutput.incomingRow1 s i).toNat + (ArrayOutput.incomingRow2 s i).toNat := by',
          '  rw [prefix_130, word0_full, word1_full, word2_full]', '',
          '/-- The actual output after an enabled second-stage edge is the weighted tree input. -/',
          'theorem captured_tree_sum (s : State) (i after : Inputs)',
          '    (enabled : i.nio_5FregEnables_5F1 = 1) :',
          '    (observe (step s i) after).nio_5Fresult = BitVec.ofNat 130 (inputPrefix130 s i) := by',
          '  rw [ArrayOutput.output_capture s i after enabled, weighted_sum_modulo, output_boundary]',
          '  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]', '', 'end ArrayTreeOutput', '']
target = root / 'lean/Proofs/ArrayTreeOutput.lean'
text = '\n'.join(lines)
if not target.exists() or target.read_text() != text:
    target.write_text(text)
print('Generated output boundary reconstruction and enabled-edge tree contract')
