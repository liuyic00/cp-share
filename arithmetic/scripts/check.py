#!/usr/bin/env python3
"""Check the arithmetic snapshot; optionally compile proof projects."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
from legacy_firrtl import check_snapshot

ROOT = Path(__file__).resolve().parent.parent
BACKENDS = ['lean', 'lean-hierarchical', 'rocq', 'rocq-bits']
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--allow-missing-generated', action='store_true', help='check a source-only checkout before regeneration')
p.add_argument('--sources', action='store_true', help='also check vendored source hashes')
p.add_argument('--build', action='store_true', help='build selected proofs (default: Lean)')
p.add_argument('--backend', choices=BACKENDS + ['all'], default='lean')
p.add_argument('--jobs', type=int, default=4, help='maximum build workers (default: 4)')
p.add_argument('--coq-switch', help='opam switch containing Coq 8.16.0')
p.add_argument('--rocq-bits-switch', help='opam switch containing Rocq 9.3.0 / Stdlib 9.2.0')
a = p.parse_args()
if a.build and a.allow_missing_generated:
    p.error('--allow-missing-generated cannot be combined with --build')
if a.jobs < 1:
    p.error('--jobs must be positive')
m = json.loads((ROOT / 'manifest.json').read_text())
selected = BACKENDS if a.backend == 'all' else [a.backend]
for name, expected in {**m['files'], **m['generated_files']}.items():
    if name.startswith('source/') and not a.sources:
        continue
    path = ROOT / name
    required = any(name.startswith((f'verification/{b}/', f'artifacts/chisel7/mlir/{b}/')) for b in selected)
    if not path.exists() and name in m['generated_files'] and (a.allow_missing_generated or not required):
        continue
    if not path.exists() and name in m['generated_files']:
        raise SystemExit('Missing generated file; run python3 scripts/regenerate.py --backend all: ' + name)
    if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
        raise SystemExit(f'snapshot mismatch: {name}')
legacy = check_snapshot(sources=a.sources)
if set(legacy['instances']) != set(m['instances']):
    raise SystemExit('Chisel 3 and Chisel 7 instance inventories differ')
for backend in selected:
    base = ROOT / 'verification' / backend
    suffix = '.lean' if backend.startswith('lean') else '.v'
    for name in m['instances']:
        model = base / 'Generated' / (name + suffix)
        if a.allow_missing_generated and str(model.relative_to(ROOT)) in m['generated_files']:
            continue
        if not model.is_file():
            raise SystemExit(f'missing model: {backend}/{name}')
    for path in base.rglob('*' + suffix):
        if 'Reference' in path.parts or '.lake' in path.parts:
            continue
        text = path.read_text()
        # Remove comments before auditing proof placeholders.
        if suffix == '.lean':
            text = re.sub(r'/\-.*?\-/', '', text, flags=re.S)
            text = re.sub(r'--[^\n]*', '', text)
            bad = r'\b(sorry|admit|axiom)\b'
            for imports in re.findall(r'^import (.+)$', text, re.M):
                for module in imports.split():
                    if module.startswith(('Generated.', 'Proofs.')):
                        target = base / (module.replace('.', '/') + suffix)
                        if a.allow_missing_generated and str(target.relative_to(ROOT)) in m['generated_files']:
                            continue
                        if not target.exists():
                            raise SystemExit(f'missing import in {path}: {module}')
        else:
            text = re.sub(r'\(\*.*?\*\)', '', text, flags=re.S)
            bad = r'\b(Admitted|admit|Axiom|Parameter)\b'
        if re.search(bad, text):
            raise SystemExit(f'proof placeholder or extra axiom: {path}')
print('Arithmetic snapshot, model inventory and proof source checks passed.', flush=True)
if a.build:
    for backend in BACKENDS if a.backend == 'all' else [a.backend]:
        command = ['lake', 'build'] if backend.startswith('lean') else ['make', f'-j{a.jobs}', 'check']
        switch = a.coq_switch if backend == 'rocq' else a.rocq_bits_switch if backend == 'rocq-bits' else None
        if switch:
            command = ['opam', 'exec', '--switch=' + switch, '--', *command]
        env = os.environ.copy()
        env['LEAN_NUM_THREADS'] = str(a.jobs)
        subprocess.run(command, cwd=ROOT / 'verification' / backend, env=env, check=True)
