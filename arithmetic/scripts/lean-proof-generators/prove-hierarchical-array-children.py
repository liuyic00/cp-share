#!/usr/bin/env python3
"""Compose the ArrayMul child assertions from the new compressor contracts."""
from pathlib import Path
import re

root = Path(__file__).resolve().parents[2] / 'verification' / 'lean-hierarchical'
text = '\n'.join(p.read_text() for p in sorted((root / 'Generated/ArrayMulDataModule').glob('Part*.lean')))
text = text[text.index('namespace nArrayMulDataModule'):]
children = dict((name, (module, state, inputs)) for name, module, state, inputs in re.findall(
    r'def (inst_\w+Eval) \(s : State\) \(i : Inputs\) : (\w+)\.Evaluation := '
    r'\w+\.evalSpec (s\.\w+\.\w+) \((\w+) s i\)', text))
contract = text[text.index('theorem asserts_of_parts'):text.index('theorem assumes_of_parts')]
order = re.findall(r'\(child\d+ : \(\((\w+) s i\)\.assertions\)', contract)
assert order and len(order) == len(children), 'Every direct instance must be covered'
lemmas = {'nC22': 'c22_asserts', 'nC32': 'c32_asserts', 'nC53': 'c53_asserts'}
lines = ['import Generated.ArrayMulDataModule', 'import Proofs.ArrayCompressors', '',
         'namespace HierarchicalArray', 'open DesignnArrayMulDataModule.nArrayMulDataModule', '',
         '/- All compressor assertions follow from their reusable contracts. Only the',
         '    two top-level pipeline assertions remain as premises here. -/',
         'set_option maxRecDepth 16384 in', 'set_option maxHeartbeats 2000000 in',
         'theorem asserts_from_pipeline (s : State) (i : Inputs)',
         '    (pipeline : localAsserts s i) : asserts s i := by',
         '  exact asserts_of_parts s i pipeline']
for name in order:
    module, state, inputs = children[name]
    lines.append(f'    ({lemmas[module]} {state} ({inputs} s i))')
lines += ['', 'end HierarchicalArray', '']
(root / 'Proofs/ArrayComposition.lean').write_text('\n'.join(lines))
print(f'Composed contracts for {len(order)} direct child instances')
