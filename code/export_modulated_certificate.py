#!/usr/bin/env python3
"""Export untrusted two-mode certificate data for independent Lean kernel checks."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def render():
    data = json.loads((ROOT/'data/modulated_certificate.json').read_text())
    lines = ['import OddCycle.Model', '',
             '/-! Generated integer data, not axioms. ModulatedFiveJob.lean checks',
             'the full operational generator and every certificate equation. -/',
             '', 'namespace OddCycle.ModulatedFiveJob', '',
             'abbrev JointState := State × Bool', '',
             'structure Witness where', '  state : JointState', '  weight : Nat', '',
             'def witnesses : List Witness := [']
    for i, row in enumerate(data['states']):
        c, d = row['state']
        queue = lambda q: '[' + ', '.join(map(str, q)) + ']'
        mode = 'true' if row['mode'] else 'false'
        comma = ',' if i + 1 < len(data['states']) else ''
        lines.append(f'  ⟨(({queue(c)}, {queue(d)}), {mode}), {row["weight"]}⟩{comma}')
    lines += [']', '', f'def totalWeight : Nat := {data["total_weight"]}', '',
              'end OddCycle.ModulatedFiveJob', '']
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    path = ROOT/'OddCycle/ModulatedCertificate.lean'
    text = render()
    if args.check:
        if path.read_text() != text:
            raise SystemExit('Stale modulated Lean certificate; rerun the exporter')
        print('PASS: modulated Lean certificate matches the integer source data.')
    else:
        path.write_text(text)
        print(f'Wrote {path.relative_to(ROOT)}')


if __name__ == '__main__':
    main()
