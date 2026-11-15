#!/usr/bin/env python3
"""Build the exact generated multiplier obligations and independently check them."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import resource
import subprocess

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / 'arithmetic/verification/firrtl2coq'

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--switch', default='firrtl2coq')
    parser.add_argument('--jobs', type=int, default=1)
    parser.add_argument('--force', action='store_true', help='Recompile the entire proof dependency closure')
    parser.add_argument('--firrtl', type=Path, default=ROOT / 'arithmetic/artifacts/chisel3/firrtl/ArrayMulDataModule8.lo.fir')
    args = parser.parse_args()
    manifest = json.loads((BASE / 'Generated/manifest.json').read_text())['ArrayMulDataModule8']
    firrtl = args.firrtl.resolve(strict=True)
    model = BASE / 'Generated/ArrayMulDataModule8.v'
    for path, key in [(firrtl, 'firrtl_sha256'), (model, 'model_sha256')]:
        if hashlib.sha256(path.read_bytes()).hexdigest() != manifest[key]:
            raise SystemExit('Generation manifest mismatch: ' + str(path))
    if manifest['obligations'] != 5:
        raise SystemExit('Expected all five generated obligations')
    opam = ['opam', 'exec', '--switch=' + args.switch, '--']
    mappings = {
        'simplssrlib': ROOT / 'tool/firrtl2coq/lib/simplssrlib',
        'nbits': ROOT / 'tool/firrtl2coq/lib/nbits',
        'firrtl': ROOT / 'tool/firrtl2coq/src',
        'ArithmeticCommon': BASE / 'Common',
        'SmallMultiplier': BASE / 'SmallMultiplier',
        'ArithmeticFIRRTL': BASE / 'Generated',
    }
    flags = []
    for name, path in mappings.items():
        flags += ['-R' if name == 'firrtl' else '-Q', str(path), name]
    sources = set()
    def visit(namespace, name):
        path = mappings[namespace] / (name.replace('.', '/') + '.v')
        if path in sources:
            return
        if not path.exists():
            raise SystemExit('Missing source: ' + str(path) + '; see firrtl2coq/README.md for generation commands.')
        sources.add(path)
        text = re.sub(r'\(\*.*?\*\)', '', path.read_text(), flags=re.S)
        if re.search(r'\b(Admitted|admit|Axiom|Parameter)\b', text):
            raise SystemExit('Unexpected admitted theorem/axiom: ' + str(path))
        for prefix, imports in re.findall(r'From\s+(\w+)\s+Require\s+(?:(?:Import|Export)\s+)?([^.]*)\.', text):
            if prefix in mappings and prefix not in {'simplssrlib', 'nbits', 'firrtl'}:
                for imported in imports.split():
                    visit(prefix, imported)
    visit('SmallMultiplier', 'Proof')
    build = ROOT / 'arithmetic/build/firrtl2coq-multiplier-proof'
    build.mkdir(parents=True, exist_ok=True)
    (build / 'result.json').unlink(missing_ok=True)
    subprocess.run(opam + ['coq_makefile', *flags, *map(str, sorted(sources)), '-o', 'Makefile'], cwd=build, check=True)
    subprocess.run(opam + ['make', '-f', 'Makefile', '-j' + str(args.jobs)] + (['-B'] if args.force else []) + ['all'], cwd=build, check=True)
    soft, hard = resource.getrlimit(resource.RLIMIT_STACK)
    resource.setrlimit(resource.RLIMIT_STACK, (min(64 * 1024 * 1024, hard) if hard != resource.RLIM_INFINITY else 64 * 1024 * 1024, hard))
    subprocess.run(opam + ['coqchk', '-silent', *flags, 'SmallMultiplier.Proof'], cwd=ROOT, check=True)
    result = {'target': 'SmallMultiplier.Proof', 'obligations': 5, 'coqchk': 'passed',
              'upstream_axioms': ['ftype_eqn_eq', 'ffield_eqn_eq'],
              'firrtl_sha256': manifest['firrtl_sha256'], 'model_sha256': manifest['model_sha256'],
              'sources_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(sources)},
              'tool_base': subprocess.check_output(['git', '-C', str(ROOT / 'tool/firrtl2coq'), 'rev-parse', 'HEAD'], text=True).strip(),
              'tool_sources_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((ROOT / 'tool/firrtl2coq/src').rglob('*.v'))}}
    (build / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    print('All 5 exact generated multiplier obligations built and checked by coqchk.')

if __name__ == '__main__':
    main()
