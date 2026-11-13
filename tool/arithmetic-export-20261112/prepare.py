#!/usr/bin/env python3
"""Extract and verify the pinned arithmetic export tools (no source checkout needed)."""
import hashlib
import json
import os
from pathlib import Path
import tarfile

ROOT = Path(__file__).resolve().parent

def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()

def prepare():
    manifest = json.loads((ROOT / 'manifest.json').read_text())
    archive = ROOT / manifest['archive']
    if digest(archive) != manifest['archive_sha256']:
        raise SystemExit('Tool archive checksum mismatch; run git lfs pull.')
    cache = ROOT / 'build' / manifest['archive_sha256']
    bundle = cache / manifest['archive_root']
    def valid():
        return all((bundle / name).is_file() and digest(bundle / name) == record['sha256']
                   for name, record in manifest['files'].items())
    if not valid():
        cache.mkdir(parents=True, exist_ok=True)
        with tarfile.open(archive, 'r:xz') as tar:
            tar.extractall(cache, filter='data')
        if not valid():
            raise SystemExit('Extracted tool checksum mismatch')
    env = os.environ.copy()
    env['LD_LIBRARY_PATH'] = str(bundle / 'lib') + (':' + env['LD_LIBRARY_PATH'] if env.get('LD_LIBRARY_PATH') else '')
    env.update(CIRCT_OPT=str(bundle / 'bin/circt-opt'),
               SPOT_PLUGIN=str(bundle / 'lib/CIRCTSpotPlugin.so'),
               FIRTOOL=str(bundle / 'bin/firtool'))
    return bundle, env

if __name__ == '__main__':
    print(prepare()[0])
