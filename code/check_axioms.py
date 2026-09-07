#!/usr/bin/env python3
"""Run the Lean axiom audits and enforce their shared release/CI allowlist."""
from __future__ import annotations

from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent.parent
AUDITS = ['Audit', 'CycleClassificationAudit', 'StructuralTheoryAudit',
          'IndistinguishabilityAudit', 'ModulatedAudit']
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def check_log(log: str) -> dict:
    """Validate actual #print axioms output; missing output is a failure."""
    dependencies = re.findall(r"depends on axioms:\s*\[([^]]*)\]", log, re.S)
    if not dependencies:
        raise RuntimeError('no axiom declarations found')
    names = {name.strip() for group in dependencies for name in group.split(',')
             if name.strip()}
    unexpected = names - ALLOWED_AXIOMS
    if unexpected:
        raise RuntimeError(f'unexpected axioms: {sorted(unexpected)}')
    if 'sorryAx' in log:
        raise RuntimeError('admitted proof dependency')
    return {'printed_declarations': len(dependencies) +
            log.count('does not depend on any axioms'), 'axioms': sorted(names)}


def main():
    for audit in AUDITS:
        print(f'Auditing OddCycle/{audit}.lean', flush=True)
        process = subprocess.run(
            ['lake', 'env', 'lean', f'OddCycle/{audit}.lean'], cwd=ROOT,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        print(process.stdout, end='', flush=True)
        process.check_returncode()
        result = check_log(process.stdout)
        print(f'PASS: {audit}: {result["printed_declarations"]} declarations; '
              f'axioms {result["axioms"]}', flush=True)


if __name__ == '__main__':
    main()
