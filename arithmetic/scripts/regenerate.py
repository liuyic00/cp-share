#!/usr/bin/env python3
"""Re-export arithmetic with pinned bundled tools; restore pinned generated models and Lean proof fragments."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from lean_proofs import generate as generate_lean_proofs

ROOT = Path(__file__).resolve().parent.parent
ENTRIES = {'lean': 'LeanEmit', 'lean-hierarchical': 'HierarchicalLeanEmit',
           'rocq': 'RocqEmit', 'rocq-bits': 'RocqBitsEmit'}

def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()

def inventory(directory):
    return {str(path.relative_to(directory)): digest(path)
            for path in sorted(directory.rglob('*'))
            if path.is_file() and path.suffix in {'.fir', '.mlir', '.lean', '.v'}}

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--backend', choices=[*ENTRIES, 'all'], default='lean')
    p.add_argument('--check', action='store_true', help='compare fresh outputs without changing tracked files')
    p.add_argument('--tool', type=Path, default=ROOT.parent / 'tool/arithmetic-export-20261112')
    a = p.parse_args()
    subprocess.run([sys.executable, str(ROOT / 'scripts/check.py'), '--sources', '--allow-missing-generated'], check=True)
    manifest_path = ROOT / 'manifest.json'
    manifest = json.loads(manifest_path.read_text())
    tool = a.tool.resolve(strict=True)
    if digest(tool / 'manifest.json') != manifest['tool_bundle']['manifest_sha256']:
        raise SystemExit('Unexpected tool manifest; select the pinned arithmetic tool bundle.')
    if digest(tool / 'prepare.py') != manifest['tool_bundle']['prepare_sha256']:
        raise SystemExit('Unexpected tool extraction helper.')
    spec = importlib.util.spec_from_file_location('arithmetic_tools', tool / 'prepare.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    _, env = module.prepare()
    env['MILL_VERSION'] = manifest['toolchains']['mill']
    (ROOT / 'build').mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='regenerate-', dir=ROOT / 'build') as work:
        staging = Path(work)
        # MLIR output-file pass options do not quote whitespace or braces.
        if any(c.isspace() or c in '{},' for c in str(staging)):
            raise SystemExit('The task path must not contain whitespace, braces or commas.')
        env['ARITHMETIC_ROOT'] = str(staging)
        backends = list(ENTRIES) if a.backend == 'all' else [a.backend]
        for backend in backends:
            subprocess.run(['./mill', '--no-server', 'Examples.runMain', 'singlefile.' + ENTRIES[backend]],
                           cwd=ROOT / 'source', env=env, check=True)
        proof_files = generate_lean_proofs(ROOT, staging, backends, manifest)
        prefixes = [prefix for backend in backends for prefix in
                    [f'artifacts/chisel7/mlir/{backend}', f'verification/{backend}/Generated']]
        produced = {prefix + '/' + name: sha for prefix in prefixes
                    for name, sha in inventory(staging / prefix).items()}
        produced.update({name: digest(staging / name) for name in proof_files})
        expected = {name: sha for name, sha in manifest['generated_files'].items()
                    if any(name.startswith(prefix + '/') for prefix in prefixes) or name in proof_files}
        if produced != expected:
            changed = sorted(name for name in produced.keys() | expected.keys()
                             if produced.get(name) != expected.get(name))
            raise SystemExit('Fresh export differs from pinned hashes:\n' + '\n'.join(changed))
        if not a.check:
            # All selected outputs passed hashes before any checkout file is replaced.
            for prefix in prefixes:
                if (ROOT / prefix).exists():
                    shutil.rmtree(ROOT / prefix)
                shutil.copytree(staging / prefix, ROOT / prefix)
            for name in proof_files:
                target = ROOT / name
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(staging / name, target)
        print('Pinned HW, models and generated Lean proofs match exactly: ' + ', '.join(backends))
        if not a.check:
            print('Generated files restored. No handwritten proofs or manifest hashes were modified.')

if __name__ == '__main__':
    main()
