#!/usr/bin/env python3
"""Rebuild the tracked FIRRTL, MLIR and Generated Lean from pinned Chisel sources."""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--mill', required=True, help='Mill launcher honoring MILL_VERSION')
    p.add_argument('--java', default='java', help='Java 17 executable')
    p.add_argument('--firtool', required=True, help='firtool 1.158.0 executable')
    p.add_argument('--tool', type=Path, default=None, help='Bundled tool directory')
    args = p.parse_args()
    manifest_path = ROOT / 'manifest.json'
    manifest = json.loads(manifest_path.read_text())
    top = manifest['top']
    args.tool = (args.tool or ROOT / manifest['tool_bundle']).resolve()
    for name, commit in manifest['source']['commits'].items():
        repo = ROOT / name
        actual = subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'], text=True).strip()
        if actual != commit:
            raise SystemExit(f'Unexpected source revision at {name}: {actual}')
        if subprocess.check_output(['git','-C',str(repo),'status','--porcelain'], text=True):
            raise SystemExit(f'Source checkout must be clean: {name}')
    spec = importlib.util.spec_from_file_location('bundled_tools', args.tool / 'export-lean.py')
    tools = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(tools)
    tool_manifest = json.loads((args.tool / 'manifest.json').read_text())
    if tool_manifest['archive_sha256'] != manifest['tool_archive_sha256']:
        raise SystemExit('Tool archive differs from the version pinned by this task')
    if tool_manifest['files']['lib/CIRCTSpotPlugin.so']['original_sha256'] != manifest['tools']['plugin_sha256']:
        raise SystemExit('Plugin identity differs from this task')
    bundle = tools.prepare()
    env = dict(os.environ)
    env['ELAN_TOOLCHAIN'] = (ROOT / 'verification/lean/lean-toolchain').read_text().strip()
    env['LD_LIBRARY_PATH'] = str(bundle / 'lib') + (':' + env['LD_LIBRARY_PATH'] if env.get('LD_LIBRARY_PATH') else '')
    firtool = shutil.which(args.firtool)
    if not firtool or 'firtool-1.158.0' not in subprocess.check_output([firtool,'--version'], text=True):
        raise SystemExit('Expected firtool 1.158.0')
    build = ROOT / 'build/regenerate'
    common = ['--source',str(ROOT / manifest['source']['path']),'--mill',args.mill,'--java',args.java]
    def run(command):
        subprocess.run(list(map(str,command)), cwd=ROOT, env=env, check=True)
    run([sys.executable, ROOT/'scripts/export.py', *common, '--firtool', firtool,
         '--circt-opt',bundle/'bin/circt-opt','--plugin',bundle/'lib/CIRCTSpotPlugin.so',
         '--output',build/'low'])
    run([sys.executable, ROOT/'scripts/export-high.py', *common,
         '--output',build/'high','--compare-low',build/'low'/f'{top}.lo.fir'])
    # Publish to the tracked locations. Never generate or overwrite Proofs.
    for source_suffix, target_suffix in [('fir','chirrtl.fir'), ('lo.fir','lo.fir'),
                                         ('flat.fir','flat.lo.fir'), ('prepared.fir','prepared.lo.fir'),
                                         ('fir2.fir','fir2.lo.fir')]:
        shutil.copyfile(build/'low'/f'{top}.{source_suffix}',ROOT/'artifacts/firrtl'/f'{top}.{target_suffix}')
    shutil.copyfile(build/'high'/f'{top}.hi.fir',ROOT/'artifacts/firrtl'/f'{top}.hi.fir')
    for suffix in ['hw.mlir','final.mlir']:
        shutil.copyfile(build/'low'/f'{top}.{suffix}',ROOT/'artifacts/mlir'/f'{top}.{suffix}')
    shutil.copyfile(build/'low'/f'{top}.lean',ROOT/'artifacts/export'/f'{top}.lean')
    # Only absolute output-directory metadata is normalized, not circuit content.
    for stage, suffix in [('low','lo.anno.json'),('high','hi.anno.json')]:
        text = (build/stage/f'{top}.anno.json').read_text()
        text = text.replace(str(ROOT), '${TASK_ROOT}')
        (ROOT/'artifacts/firrtl'/f'{top}.{suffix}').write_text(text)
    manifest['sha256'] = {}
    for directory in ['artifacts','verification','scripts','counterexamples']:
        for file in sorted((ROOT/directory).rglob('*')):
            if file.is_file() and not any(x in file.parts for x in ['.lake','__pycache__']):
                manifest['sha256'][str(file.relative_to(ROOT))] = hashlib.sha256(file.read_bytes()).hexdigest()
    manifest_path.write_text(json.dumps(manifest,indent=2,ensure_ascii=False)+'\n')
    print('Tracked artifacts and Generated Lean updated. Review git diff; then run python3 scripts/check.py --build.')

if __name__ == '__main__':
    main()
