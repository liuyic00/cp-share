#!/usr/bin/env python3
"""Generate grouped capture/hold contracts for actual first-stage register bits."""
from pathlib import Path
import re
from collections import defaultdict
root = Path(__file__).resolve().parents[2] / 'verification' / 'lean-hierarchical'
text = '\n'.join(p.read_text() for p in sorted((root/'Generated/ArrayMulDataModule').glob('Part*.lean')))
text = text[text.index('namespace nArrayMulDataModule'):]
registers = re.findall(r'def (v\d+) \(s : State\) \(i : Inputs\) : BitVec 1 := if i.nio_5FregEnables_5F0 = 1 then \((v\d+) s i\) else s\.(g\d+\.r\w+)', text)
assert len(registers) == 2278, len(registers)
groups = defaultdict(list)
for nxt, source, field in registers:
    groups[int(field.split('.')[0][1:])].append((nxt, source, field))
dest = root/'Proofs/ArrayCapture'
dest.mkdir(exist_ok=True)
imports = []
for group, entries in sorted(groups.items()):
    name = f'Group{group:03d}'
    imports.append(f'import Proofs.ArrayCapture.{name}')
    state = f'firstGroup{group}State'
    inputs = f'firstGroup{group}Input'
    lines = ['import Generated.ArrayMulDataModule', '', 'namespace HierarchicalArray',
             'open DesignnArrayMulDataModule.nArrayMulDataModule', '',
             f'def {state} (s : State) : List (BitVec 1) :=',
             '  [' + ', '.join('s.'+field for _,_,field in entries) + ']', '',
             f'def {inputs} (s : State) (i : Inputs) : List (BitVec 1) :=',
             '  [' + ', '.join(f'{source} s i' for _,source,_ in entries) + ']', '']
    for action, enabled, rhs in [('capture',1,f'{inputs} s i'),('hold',0,f'{state} s')]:
        lines += [f'theorem first_group_{group}_{action} (s : State) (i : Inputs)',
                  f'    (enabled : i.nio_5FregEnables_5F0 = {enabled}) :',
                  f'    {state} (step s i) = {rhs} := by',
                  f'  simp only [{state}, step, eval_eq_spec]',
                  '  change [' + ', '.join(f'{nxt} s i' for nxt,_,_ in entries) + '] = _',
                  '  simp only [' + ', '.join(nxt for nxt,_,_ in entries) + f', {inputs}, enabled]',
                  '  rfl', '']
    lines += ['end HierarchicalArray', '']
    (dest/(name+'.lean')).write_text('\n'.join(lines))
(root/'Proofs/ArrayCapture.lean').write_text('\n'.join(imports)+'\n')
print(f'Generated {len(groups)} capture/hold groups covering {len(registers)} register bits')

registers = re.findall(r'def (v\d+) \(s : State\) \(i : Inputs\) : BitVec 1 := if i.nio_5FregEnables_5F1 = 1 then (.+) else s\.(g\d+\.r\w+)', text)
registers = [r for r in registers if 'nresultKnown' not in r[2]]
assert len(registers) == 256, len(registers)
groups = defaultdict(list)
for nxt, source, field in registers:
    groups[int(field.split('.')[0][1:])].append((nxt, source, field))
dest = root/'Proofs/ArrayTransfer'
dest.mkdir(exist_ok=True)
imports = []
for group, entries in sorted(groups.items()):
    name = f'Group{group:03d}'
    imports.append(f'import Proofs.ArrayTransfer.{name}')
    state = f'secondGroup{group}State'
    inputs = f'secondGroup{group}Input'
    lines = ['import Generated.ArrayMulDataModule', '', 'namespace HierarchicalArray',
             'open DesignnArrayMulDataModule.nArrayMulDataModule', '',
             f'def {state} (s : State) : List (BitVec 1) :=',
             '  [' + ', '.join('s.'+field for _,_,field in entries) + ']', '',
             f'def {inputs} (s : State) (i : Inputs) : List (BitVec 1) :=',
             '  [' + ', '.join(source for _,source,_ in entries) + ']', '']
    for action, enabled, rhs in [('capture',1,f'{inputs} s i'),('hold',0,f'{state} s')]:
        lines += [f'theorem second_group_{group}_{action} (s : State) (i : Inputs)',
                  f'    (enabled : i.nio_5FregEnables_5F1 = {enabled}) :',
                  f'    {state} (step s i) = {rhs} := by',
                  f'  simp only [{state}, step, eval_eq_spec]',
                  '  change [' + ', '.join(f'{nxt} s i' for nxt,_,_ in entries) + '] = _',
                  '  simp only [' + ', '.join(nxt for nxt,_,_ in entries) + ', ' +
                    (f'{inputs}, ' if action == 'capture' else '') + 'enabled]',
                  '  rfl', '']
    lines += ['end HierarchicalArray', '']
    (dest/(name+'.lean')).write_text('\n'.join(lines))
(root/'Proofs/ArrayTransfer.lean').write_text('\n'.join(imports)+'\n')
print(f'Generated {len(groups)} transfer/hold groups covering {len(registers)} register bits')
