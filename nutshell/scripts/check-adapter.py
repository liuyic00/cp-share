#!/usr/bin/env python3
"""Check the actual legacy FIRRTL adapter on a small memory/initial-state circuit."""
import argparse
from pathlib import Path
import re
import subprocess

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--output', type=Path, required=True)
p.add_argument('--java', required=True)
p.add_argument('--classpath', required=True)
p.add_argument('--firtool', required=True)
p.add_argument('--circt-opt', required=True)
p.add_argument('--plugin', required=True)
p.add_argument('--lean', default='lean')
a = p.parse_args()
out = a.output.resolve()
out.mkdir(parents=True, exist_ok=True)
fixture = Path(__file__).with_name('memory-test.fir')
subprocess.run([a.java, '-cp', a.classpath, 'ExportNutShell', str(out), str(fixture)], check=True)
f = out / 'NutCore.prepared.fir'
f.write_text(f.read_text().replace('FIRRTL version 1.2.0', 'FIRRTL version 2.0.0', 1))
hw, model = out / 'MemoryFixture.mlir', out / 'MemoryFixture.lean'
subprocess.run([a.firtool, str(f), '--ir-hw', '--disable-opt', '--lower-to-core',
                '--verification-flavor=immediate', '-o', str(hw)], check=True)
subprocess.run([a.circt_opt, str(hw), '--load-pass-plugin=' + a.plugin,
                '--pass-pipeline=builtin.module(strip-om,export-lean{output-file=' + str(model) + '})',
                '-o', '/dev/null'], check=True)
s = model.read_text()
state = re.search(r'structure State where\n(.*?)  deriving', s, re.S)[1]
inputs = re.search(r'structure Inputs where\n(.*?)  deriving', s, re.S)[1]
fields = re.findall(r'^  (\w+) : BitVec (\d+)', state, re.M)
assert len(fields) == 10, fields
values = {}
for name, width in fields:
    match = re.search(r'n(ram|rom)_5Fword_5F(\d+)$', name)
    values[name] = (10 if match[1] == 'ram' else 20) + int(match[2]) if match else 0
input_names = re.findall(r'^  (\w+) : BitVec \d+', inputs, re.M)
init_names = [n for n in input_names if 'invalid' in n]
assert len(init_names) == 1, init_names
base = {n: 0 for n in input_names}
base.update(nreset=0, naddr=2, ndata=99, nwen=1, nmask=1, nren=1)
for n in base:
    if 'disabled' in n: base[n] = 77
base[init_names[0]] = 57
record = lambda d: '{' + ', '.join(f'{k} := {v}' for k, v in d.items()) + '}'
proof = f'''\nnamespace AdapterChecks
open nMemoryFixture
def initial : State := {record(values)}
def input : Inputs := {record(base)}
example : (observe initial input).nvalue = 12 ∧
          (observe initial input).nromvalue = 22 := by decide
example : (observe (step initial input) input).nvalue = 99 ∧
          (observe (step initial input) input).nromvalue = 22 := by decide
example : (observe (step initial {{ input with nmask := 0 }}) input).nvalue = 12 := by decide
example : (observe (step initial {{ input with nwen := 0 }}) input).nvalue = 12 := by decide
example : (observe (step initial input) {{ input with naddr := 1 }}).nvalue = 11 := by decide
example : (observe initial {{ input with nren := 0 }}).nvalue = 77 := by decide
example : (observe (step initial {{ input with nreset := 1 }}) input).nsharedA = 57 ∧
          (observe (step initial {{ input with nreset := 1 }}) input).nsharedB = 57 := by decide
end AdapterChecks
'''
model.write_text(s + proof)
subprocess.run([a.lean, str(model)], check=True)
print('Memory read/write/mask/hold and shared arbitrary initialization kernel checks passed.')
