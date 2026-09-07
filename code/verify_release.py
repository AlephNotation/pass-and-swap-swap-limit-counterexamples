#!/usr/bin/env python3
"""Replay the consolidated verification; keep commands, statuses and input hashes.

Usage: python3 code/verify_release.py --output-dir /tmp/cycle-verification
Requires the pinned Lean environment, Python 3.10+, Tectonic and Poppler.
Does not publish, change proofs, or regenerate committed expected results.
Visual and mathematical review are recorded separately by the reviewer.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shlex
import subprocess
import sys
import time

from check_axioms import AUDITS, check_log

ROOT = Path(__file__).resolve().parent.parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inputs():
    paths = [ROOT / p for p in ['OddCycle.lean', 'lakefile.toml',
             'lake-manifest.json', 'lean-toolchain', 'paper.tex', 'paper.pdf',
             'README.md', 'LEAN.md', 'PACKAGE.md', 'CITATION.cff',
             'run_checks.py', 'verification/ManuscriptStatements.lean']]
    for directory, pattern in [('OddCycle', '*.lean'), ('code', '*.py'),
                               ('data', '*.json'), ('results', '*.json'),
                               ('docs', '*.md')]:
        paths.extend((ROOT / directory).glob(pattern))
    return sorted(paths)


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, required=True)
    args = parser.parse_args()
    out = args.output_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    source_commit = ((ROOT/'SOURCE_COMMIT.txt').read_text().strip()
                     if (ROOT/'SOURCE_COMMIT.txt').exists() else
                     subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip())
    hashes = {str(p.relative_to(ROOT)): digest(p) for p in inputs()}
    (out/'input_sha256.json').write_text(json.dumps(hashes, indent=2)+'\n')
    report = {'source_commit': source_commit,
              'started_utc': datetime.now(timezone.utc).isoformat(),
              'commands': [], 'internal_checks': [], 'status': 'RUNNING'}

    def save():
        (out/'checks.json').write_text(json.dumps(report, indent=2)+'\n')

    def run(name, command):
        print(f'{name}: {shlex.join(command)}', flush=True)
        begin = time.monotonic()
        with (out/(name+'.log')).open('w') as log:
            process = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
        record = {'name': name, 'command': command, 'cwd': str(ROOT),
                  'exit_code': process.returncode,
                  'seconds': round(time.monotonic()-begin, 3), 'log': name+'.log'}
        report['commands'].append(record)
        save()
        require(process.returncode == 0, f'{name} failed; see {out/(name+".log")}')
        print(f'  PASS ({record["seconds"]} s)', flush=True)

    def checked(name, details):
        report['internal_checks'].append({'name': name, 'status': 'PASS', 'details': details})
        save()

    save()
    try:
        for name, command in [('lean-version', ['lake', 'env', 'lean', '--version']),
                              ('python-version', [sys.executable, '--version']),
                              ('tex-version', ['tectonic', '--version']),
                              ('poppler-version', ['pdftoppm', '-v'])]:
            run(name, command)
        run('lean-build', ['lake', 'build'])
        run('manuscript-statements', ['lake', 'env', 'lean', 'verification/ManuscriptStatements.lean'])
        for audit in AUDITS:
            run('axioms-'+audit, ['lake', 'env', 'lean', 'OddCycle/'+audit+'.lean'])
            log = (out/('axioms-'+audit+'.log')).read_text()
            checked('axiom-set-'+audit, check_log(log))
        run('kernel-replay', ['lake', 'env', 'leanchecker', '--verbose', 'OddCycle'])
        run('python-suite', [sys.executable, '-B', 'run_checks.py'])
        run('python-suite-optimized', [sys.executable, '-B', '-O', 'run_checks.py'])
        run('lean-certificate-export', [sys.executable, '-B', 'code/export_lean_certificate.py', '--check'])
        run('modulated-lean-export', [sys.executable, '-B', 'code/export_modulated_certificate.py', '--check'])
        generated = out/'regenerated_certificate.json'
        run('certificate-regeneration', [sys.executable, '-B', 'code/regenerate_certificate.py', '--output', str(generated)])
        run('regenerated-certificate-verification', [sys.executable, '-B', 'code/verify_five.py', '--certificate', str(generated)])
        require(json.loads(generated.read_text()) == json.loads((ROOT/'data/stationary_certificate.json').read_text()),
                'regenerated certificate differs from committed certificate')
        checked('certificate-exact-equality', 'Regenerated and supplied JSON objects are identical.')
        modulated = out/'regenerated_modulated_certificate.json'
        run('modulated-certificate-regeneration', [sys.executable, '-B', 'code/regenerate_modulated_certificate.py', '--output', str(modulated)])
        run('modulated-certificate-verification', [sys.executable, '-B', 'code/verify_modulated.py', '--certificate', str(modulated)])
        require(json.loads(modulated.read_text()) == json.loads((ROOT/'data/modulated_certificate.json').read_text()),
                'regenerated modulated certificate differs from committed certificate')
        checked('modulated-certificate-exact-equality', 'Regenerated and supplied modulated JSON objects are identical.')

        paper_dir = out/'paper'
        paper_dir.mkdir(exist_ok=True)
        for i in (1, 2):
            run(f'paper-build-{i}', ['tectonic', '--keep-logs', '--keep-intermediates',
                                    '--outdir', str(paper_dir), 'paper.tex'])
        texlog = (paper_dir/'paper.log').read_text()
        require(not re.search(r'Overfull|Underfull|LaTeX Warning:|Package .* Warning:', texlog),
                'final TeX log has a warning or box problem')
        source = (ROOT/'paper.tex').read_text()
        labels = re.findall(r'\\label\{([^}]+)\}', source)
        references = re.findall(r'\\(?:ref|eqref)\{([^}]+)\}', source)
        require(len(labels) == len(set(labels)), 'duplicate manuscript labels')
        require(set(references) <= set(labels), 'unresolved source reference')
        checked('manuscript-references', f'{len(labels)} unique labels; every internal reference resolves; final TeX log clean.')
        for name, pdf in [('committed', ROOT/'paper.pdf'), ('rebuilt', paper_dir/'paper.pdf')]:
            (out/name).mkdir(exist_ok=True)
            run('render-'+name, ['pdftoppm', '-r', '110', '-png', str(pdf), str(out/name/'page')])
        committed = sorted((out/'committed').glob('page-*.png'))
        rebuilt = sorted((out/'rebuilt').glob('page-*.png'))
        require(len(committed) == len(rebuilt) > 0, 'PDF page counts differ')
        require([digest(p) for p in committed] == [digest(p) for p in rebuilt],
                'committed and rebuilt PDF renderings differ')
        checked('render-equivalence', {'pages': len(committed), 'dpi': 110,
                                      'result': 'All committed/rebuilt PNG page hashes agree.'})

        after = {str(p.relative_to(ROOT)): digest(p) for p in inputs()}
        require(hashes == after, 'verification inputs changed during the run')
        checked('inputs-unchanged', f'{len(hashes)} source/artifact/input files unchanged during verification.')
        report['status'] = 'PASS'
    except Exception as exc:
        report['status'] = 'FAIL'
        report['error'] = str(exc)
        raise
    finally:
        report['finished_utc'] = datetime.now(timezone.utc).isoformat()
        save()
    print('PASS: complete automated verification. Mathematical and visual review are recorded separately.', flush=True)


if __name__ == '__main__':
    main()
