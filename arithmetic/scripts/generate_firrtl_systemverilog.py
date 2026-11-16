#!/usr/bin/env python3
"""Generate the proved XiangShan instances' SystemVerilog from pinned Low FIRRTL."""
import argparse
import hashlib
import os
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
NAMES = ('Radix2Divider', 'ArrayMulDataModule8')
OPTIONS = ['-X', 'sverilog']


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true',
                        help='Regenerate in a temporary directory and compare committed outputs')
    args = parser.parse_args()
    legacy = json.loads((ROOT / 'legacy-manifest.json').read_text())
    for filename, expected in legacy['sources'].items():
        if digest(ROOT / filename) != expected:
            raise SystemExit('Unexpected legacy source file: ' + filename)
    env = dict(os.environ, MILL_VERSION=legacy['mill'])
    output = ROOT / 'artifacts/chisel3/systemverilog'
    records = {
        'compiler': 'firrtl.stage.FirrtlMain',
        'toolchain': {key: legacy[key] for key in ('firrtl', 'scala', 'mill', 'jdk')},
        'options': OPTIONS,
        'instances': {},
    }
    (ROOT / 'build').mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='firrtl-systemverilog-', dir=ROOT / 'build') as tmp:
        staging = Path(tmp)
        for name in NAMES:
            source = ROOT / f'artifacts/chisel3/firrtl/{name}.lo.fir'
            source_name = str(source.relative_to(ROOT))
            if digest(source) != legacy['outputs'][source_name]:
                raise SystemExit('Pinned FIRRTL checksum mismatch: ' + source_name)
            target = staging / (name + '.sv')
            subprocess.run(['./mill', '--no-server', 'Examples.runMain',
                            'firrtl.stage.FirrtlMain', *OPTIONS, '-i', str(source),
                            '--target-dir', str(staging), '-o', target.name],
                           cwd=ROOT / 'source-legacy', env=env, check=True)
            records['instances'][name] = {
                'width': legacy['instances'][name],
                'firrtl': source_name,
                'firrtl_sha256': digest(source),
                'systemverilog': target.name,
                'systemverilog_sha256': digest(target),
            }
        (staging / 'manifest.json').write_text(json.dumps(records, indent=2) + '\n')
        for filename in [*(name + '.sv' for name in NAMES), 'manifest.json']:
            fresh, saved = staging / filename, output / filename
            if args.check:
                if not saved.exists() or fresh.read_bytes() != saved.read_bytes():
                    raise SystemExit('Fresh SystemVerilog export differs: ' + str(saved))
            else:
                output.mkdir(parents=True, exist_ok=True)
                saved.write_bytes(fresh.read_bytes())
    print('Pinned SystemVerilog ' + ('matches exactly.' if args.check else 'generated.'))


if __name__ == '__main__':
    main()
