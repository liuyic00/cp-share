#!/usr/bin/env python3
"""Reproduce the Scala FIRRTL 1.6 / Chisel 3.6 High/Low FIRRTL snapshots."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def check_snapshot(sources=False):
    manifest = json.loads((ROOT / 'legacy-manifest.json').read_text())
    expected = {f'artifacts/chisel3/firrtl/{name}.{stage}.fir'
                for name in manifest['instances'] for stage in ('hi', 'lo')}
    if set(manifest['outputs']) != expected:
        raise SystemExit('Incomplete legacy High/Low inventory')
    actual = {str(p.relative_to(ROOT)) for p in (ROOT / 'artifacts/chisel3/firrtl').glob('*.fir')}
    if actual != expected:
        raise SystemExit('Unexpected legacy FIRRTL inventory')
    entries = dict(manifest['outputs'])
    if sources:
        entries.update(manifest['sources'])
    for name, expected_hash in entries.items():
        path = ROOT / name
        if not path.is_file() or digest(path) != expected_hash:
            raise SystemExit('Legacy snapshot mismatch: ' + name)
    return manifest


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--check', action='store_true', help='regenerate in build/ and compare without replacing artifacts')
    args = p.parse_args()
    manifest = json.loads((ROOT / 'legacy-manifest.json').read_text())
    for name, expected in manifest['sources'].items():
        if digest(ROOT / name) != expected:
            raise SystemExit('Legacy source checksum mismatch: ' + name)
    (ROOT / 'build').mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='legacy-', dir=ROOT / 'build') as temp:
        env = dict(os.environ, ARITHMETIC_ROOT=temp, MILL_VERSION=manifest['mill'])
        subprocess.run(['./mill', '--no-server', 'Examples.runMain', 'LegacyEmit'],
                       cwd=ROOT / 'source-legacy', env=env, check=True)
        for name, expected in manifest['outputs'].items():
            fresh = Path(temp) / name
            if digest(fresh) != expected:
                raise SystemExit('Legacy generation differs from pinned snapshot: ' + name)
            target = ROOT / name
            if args.check:
                if digest(target) != expected:
                    raise SystemExit('Legacy saved snapshot differs: ' + name)
            else:
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(fresh.read_bytes())
    check_snapshot(sources=True)
    print(f"All {len(manifest['instances'])} legacy High/Low FIRRTL snapshot pairs match exactly.")

if __name__ == '__main__':
    main()
