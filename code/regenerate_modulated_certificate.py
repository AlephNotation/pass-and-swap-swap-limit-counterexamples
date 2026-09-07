#!/usr/bin/env python3
"""Regenerate the exact C5 certificate with budgets 2/infinity and unit switching."""
import argparse
from fractions import Fraction
import json
from math import gcd, lcm
from pathlib import Path

from regenerate_certificate import (TRAP, actions, canonical, service_rate,
                                    solve_exact, symmetry, transition)


def make_certificate():
    reps = sorted({canonical(s) for s in TRAP})
    index = {s: i for i, s in enumerate(reps)}
    size = len(reps)
    if size != 45 or any(len({symmetry(s, e, f) for e in (1, -1)
                             for f in (0, 1)}) != 4 for s in reps):
        raise RuntimeError('Expected 45 free symmetry orbits in each mode')
    q = [[0] * (2 * size) for _ in range(2 * size)]
    for mode in (0, 1):
        for i, s in enumerate(reps):
            row = mode * size + i
            for side, pos in actions(s):
                rate = int(service_rate(s, side, pos, Fraction(2)))
                # Five replacements are sufficient for every five-job queue.
                t = transition(s, side, pos, 2 if mode == 0 else 5)
                q[row][mode * size + index[canonical(t)]] += rate
                q[row][row] -= rate
            q[row][(1 - mode) * size + i] += 1
            q[row][row] -= 1
    matrix = [list(row) for row in zip(*q)]
    matrix[-1] = [1] * (2 * size)
    p = solve_exact(matrix, [0] * (2 * size - 1) + [1])
    pi = {(s, b): p[b * size + index[canonical(s)]] / 4
          for s in TRAP for b in (0, 1)}
    denominator = lcm(*(v.denominator for v in pi.values()))
    weights = {s: int(v * denominator) for s, v in pi.items()}
    divisor = gcd(*weights.values())
    weights = {s: v // divisor for s, v in weights.items()}
    return {
        'model': 'C5; budgets 2 and unlimited; class rates (2,1,1,1,1) in both queues; independent mode switching at rate one in each direction',
        'switch_rate': 1,
        'total_weight': sum(weights.values()),
        'states': [{'state': s, 'mode': b, 'weight': weights[(s, b)]}
                   for b in (0, 1) for s in sorted(TRAP)],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    certificate = make_certificate()
    from verify_modulated import verify_certificate
    result = verify_certificate(certificate)
    args.output.write_text(json.dumps(certificate, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
