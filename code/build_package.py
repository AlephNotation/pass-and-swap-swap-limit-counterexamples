#!/usr/bin/env python3
"""Package committed sources together with a successful verification run.

Usage: python3 code/build_package.py --verification-dir /tmp/cycle-verification \
    --output /tmp/cycle-verification.tar.gz
The archive adds SOURCE_COMMIT.txt and a SHA256SUMS covering all regular
files. Generated evidence is included under verification/evidence/ in the
archive, not tracked in Git. Checked input hashes must match the committed
sources; unrelated local modifications and untracked files are not included.
"""
import argparse
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess
import tarfile

from verify_release import inputs

ROOT = Path(__file__).resolve().parent.parent


def add_evidence(files, directory):
    """Require a completed run for these sources before copying its evidence."""
    report = json.loads((directory/'checks.json').read_text())
    if report['status'] != 'PASS':
        raise RuntimeError('Verification run did not pass')
    hashes = json.loads((directory/'input_sha256.json').read_text())
    expected = {str(p.relative_to(ROOT)) for p in inputs()}
    if set(hashes) != expected:
        raise RuntimeError('Verification input list differs from the current verifier')
    for name, digest in hashes.items():
        if name not in files or hashlib.sha256(files[name]).hexdigest() != digest:
            raise RuntimeError(f'Verification does not match committed input: {name}')
    if not report['commands']:
        raise RuntimeError('Verification has no command records')
    for command in report['commands']:
        if command['exit_code'] != 0 or not (directory/command['log']).is_file():
            raise RuntimeError(f'Missing or failed verification command: {command["name"]}')
    for path in sorted(directory.rglob('*')):
        if path.is_symlink():
            raise RuntimeError(f'Unsupported evidence symlink: {path}')
        if path.is_file():
            name = 'verification/evidence/'+path.relative_to(directory).as_posix()
            if name in files:
                raise RuntimeError(f'Evidence is already tracked: {name}')
            files[name] = path.read_bytes()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--verification-dir', required=True, type=Path)
    args = parser.parse_args()
    evidence = args.verification_dir.resolve()
    output = args.output.resolve()
    if output.is_relative_to(evidence):
        raise RuntimeError('Package output must be outside the verification directory')
    commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    original = subprocess.check_output(['git', 'archive', '--format=tar', commit], cwd=ROOT)
    files = {}
    modes = {}
    with tarfile.open(fileobj=io.BytesIO(original)) as archive:
        for member in archive:
            if member.isfile():
                files[member.name] = archive.extractfile(member).read()
                modes[member.name] = member.mode
            elif not member.isdir():
                raise RuntimeError(f'Unsupported archive entry: {member.name}')
    add_evidence(files, evidence)
    files['SOURCE_COMMIT.txt'] = (commit+'\n').encode()
    files['SHA256SUMS'] = ''.join(
        f'{hashlib.sha256(data).hexdigest()}  {name}\n'
        for name, data in sorted(files.items())).encode()
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open('wb') as raw, gzip.GzipFile(fileobj=raw, mode='wb', filename='', mtime=0) as zipped:
        with tarfile.open(fileobj=zipped, mode='w') as archive:
            for name, data in sorted(files.items()):
                info = tarfile.TarInfo('cycle-classification/'+name)
                info.size = len(data)
                info.mode = modes.get(name, 0o644)
                info.mtime = 0
                archive.addfile(info, io.BytesIO(data))
    digest = hashlib.sha256(output.read_bytes()).hexdigest()
    output.with_suffix(output.suffix+'.sha256').write_text(f'{digest}  {output.name}\n')
    print(f'{commit}: {len(files)} files -> {output}')
    print(f'SHA256 {digest}')


if __name__ == '__main__':
    main()
