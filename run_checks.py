#!/usr/bin/env python3
"""Run every packaged exact check and compare to the recorded results.

Python 3.10+; no third-party dependencies. Run from any working directory:
    python3 run_checks.py
    python3 -O run_checks.py
Default: verify data files without modifying them; fail on stale expected output.
--output-dir DIR writes fresh JSON copies after successful comparison.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path,
                        help='optionally write fresh results into this directory')
    args = parser.parse_args()
    if sys.version_info < (3, 10):
        print('Python 3.10 or newer is required.', file=sys.stderr)
        return 2
    options = ['-B'] + (['-O'] if sys.flags.optimize else [])
    tests = [
        ('five_job', 'verify_five.py', ['--certificate', str(ROOT/'data/stationary_certificate.json')]),
        ('orbits', 'verify_orbits.py', []),
        ('uniform', 'verify_uniform.py', []),
        ('classification', 'verify_classification.py', []),
        ('head_cycles', 'verify_head_cycles.py', []),
        ('nine_job', 'verify_nine.py', []),
        ('screen', 'verify_screen.py', []),
    ]
    try:
        for name, script, arguments in tests:
            print(f'Checking {name} ...', flush=True)
            result = subprocess.run([sys.executable, *options, str(ROOT/'code'/script), *arguments],
                                    cwd=ROOT, capture_output=True, text=True, check=True)
            data = json.loads(result.stdout)
            if data.get('status') != 'PASS':
                raise ValueError(f'{name} did not report PASS')
            expected = json.loads((ROOT/'results'/f'{name}.json').read_text())
            if data != expected:
                raise ValueError(f'{name}: fresh output differs from recorded results')
            if args.output_dir:
                args.output_dir.mkdir(parents=True, exist_ok=True)
                (args.output_dir/f'{name}.json').write_text(json.dumps(data, indent=2)+'\n')
            print(f'  PASS; reproduced results/{name}.json', flush=True)
        print('PASS: every packaged check completed and every expected result was reproduced.')
        return 0
    except subprocess.CalledProcessError as exc:
        print(exc.stdout, file=sys.stderr)
        print(exc.stderr, file=sys.stderr)
        return exc.returncode or 1
    except (ValueError, OSError) as exc:
        print(f'FAIL: {exc}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
