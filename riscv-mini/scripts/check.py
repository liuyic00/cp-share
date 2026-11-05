#!/usr/bin/env python3
"""Check pinned artifacts/proof sources, declaration identity, and optionally build Lean."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent.parent

def check(task, build, sources):
    root = ROOT
    report = json.loads((root / 'manifest.json').read_text())
    for name, digest in report['sha256'].items():
        path = root / name
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise SystemExit(f'{task}: hash mismatch: {name}')
    for directory in ['verification/lean/Generated', 'verification/lean/Proofs']:
        actual = {str(p.relative_to(root)) for p in (root / directory).rglob('*.lean')}
        expected = {n for n in report['sha256'] if n.startswith(directory + '/') and n.endswith('.lean')}
        if actual != expected:
            raise SystemExit(f'{task}: unexpected/missing Lean files in {directory}')
    top = report['top']
    namespace = 'n' + top
    def body(text):
        return text.split(f'namespace {namespace}\n', 1)[1].rsplit(f'end {namespace}', 1)[0]
    raw = (root / 'artifacts/export' / f'{top}.lean').read_text()
    parts = sorted((root / 'verification/lean/Generated' / top).glob('Part*.lean'))
    if ''.join(body(p.read_text()) for p in parts) != body(raw):
        raise SystemExit(f'{task}: generated partitions differ from monolithic export')
    for stage in ['hi', 'nomem.hi', 'lo', 'flat.lo', 'prepared.lo']:
        text = (root / 'artifacts/firrtl' / f'{top}.{stage}.fir').read_text()
        for kind, count in report['properties'].items():
            if len(re.findall(r'^\s*' + kind + r'\(', text, re.M)) != count:
                raise SystemExit(f'{task}: {stage} {kind} count mismatch')
    nomem = (root / 'artifacts/firrtl' / f'{top}.nomem.hi.fir').read_text()
    if re.search(r'^\s*(?:mem|cmem|smem)\s+[^\s:]+\s*:', nomem, re.M):
        raise SystemExit(f'{task}: memory remains in nomem High FIRRTL')
    for memory in ['imem', 'dmem']:
        if len(re.findall(r'^\s*reg ' + memory + r'_word_\d+ : UInt<32>', nomem, re.M)) != 16:
            raise SystemExit(f'{task}: wrong {memory} register count in nomem High FIRRTL')
    for kind, count in report['properties'].items():
        text = (root / 'artifacts/mlir' / f'{top}.final.mlir').read_text()
        if len(re.findall(r'verif.clocked_' + kind + r'\b', text)) != count:
            raise SystemExit(f'{task}: final MLIR {kind} count mismatch')
    if sources:
        for path, commit in report['source']['commits'].items():
            actual = subprocess.check_output(['git', '-C', str(root / path), 'rev-parse', 'HEAD'], text=True).strip()
            if actual != commit:
                raise SystemExit(f'{task}: wrong source commit at {path}: {actual}')
            changed = subprocess.check_output(['git', '-C', str(root / path), 'status', '--porcelain', '--untracked-files=all'], text=True)
            if changed:
                raise SystemExit(f'{task}: modified source checkout: {path}\n{changed}')
    print(f'{task}: hashes, Lean declaration identity, and property counts OK', flush=True)
    if build:
        subprocess.run(['lake', 'build'], cwd=root / 'verification/lean', check=True)
        result = subprocess.run(['lake', 'env', 'lean', report['proof']['entry']],
                                cwd=root / 'verification/lean', text=True, capture_output=True, check=True)
        print(result.stdout, end='')
        axioms = re.findall(r'depends on axioms:\s*\[([^]]*)\]', result.stdout)
        if not axioms or any(set(x.strip() for x in a.split(',') if x.strip()) -
                             {'propext', 'Classical.choice', 'Quot.sound'} for a in axioms):
            raise SystemExit(f'{task}: unexpected or missing final axiom report')
        print(f'{task}: final theorem checked; scope: {report["proof"]["scope"]}')

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build', action='store_true')
    parser.add_argument('--sources', action='store_true')
    args = parser.parse_args()
    check(ROOT.name, args.build, args.sources)
