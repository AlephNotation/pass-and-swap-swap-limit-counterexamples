#!/usr/bin/env python3
"""Package a committed revision, preserving every tracked source and certificate.

Usage: python3 code/build_package.py --output /tmp/cycle-verification.tar.gz
The archive adds SOURCE_COMMIT.txt and a SHA256SUMS covering all regular
files. Local modifications and untracked files are never silently included.
"""
import argparse
import gzip
import hashlib
import io
from pathlib import Path
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parent.parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
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
    files['SOURCE_COMMIT.txt'] = (commit+'\n').encode()
    files['SHA256SUMS'] = ''.join(
        f'{hashlib.sha256(data).hexdigest()}  {name}\n'
        for name, data in sorted(files.items())).encode()
    output = args.output.resolve()
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
