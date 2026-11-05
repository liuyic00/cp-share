#!/usr/bin/env python3
"""Export HW MLIR using the checksum-pinned bundled Linux tools."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def prepare():
    manifest = json.loads((ROOT / 'manifest.json').read_text())
    archive = ROOT / manifest['archive']
    if digest(archive) != manifest['archive_sha256']:
        raise SystemExit('Archive checksum mismatch')
    cache = ROOT / 'build' / manifest['archive_sha256']
    bundle = cache / manifest['archive_root']
    def valid():
        return all((bundle / name).is_file() and digest(bundle / name) == record['sha256']
                   for name, record in manifest['files'].items())
    if not valid():
        cache.mkdir(parents=True, exist_ok=True)
        subprocess.run(['tar', '-xJf', str(archive), '-C', str(cache)], check=True)
        if not valid():
            raise SystemExit('Extracted tool checksum mismatch')
    return bundle


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    bundle = prepare()
    source = args.input.resolve(strict=True)
    output = args.output.resolve()
    if any(c in str(output) for c in '{}') or any(c.isspace() for c in str(output)):
        raise SystemExit('Output path must not contain whitespace or braces (MLIR pipeline syntax)')
    output.parent.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ)
    env['LD_LIBRARY_PATH'] = str(bundle / 'lib') + (':' + env['LD_LIBRARY_PATH'] if env.get('LD_LIBRARY_PATH') else '')
    subprocess.run([str(bundle / 'bin/circt-opt'), str(source),
                    '--load-pass-plugin=' + str(bundle / 'lib/CIRCTSpotPlugin.so'),
                    '--mlir-print-op-on-diagnostic=false',
                    '--pass-pipeline=builtin.module(strip-om,export-lean{output-file=' + str(output) + '})',
                    '-o', str(output.with_suffix('.final.mlir'))], env=env, check=True)

if __name__ == '__main__':
    main()
