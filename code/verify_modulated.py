#!/usr/bin/env python3
"""Independently verify all 360 states of the two-mode C5 stationary certificate.

Mode 0 has budget two; mode 1 is unlimited. Both switches have rate one.
Checks use integer arithmetic, original-position transitions, and a second
carry implementation. The verifier does not call the stationary solver.
"""
import argparse
from itertools import permutations
import json
from math import comb
from pathlib import Path

from verify_five import balanced, check, complete, complete_carried, transition

ROOT = Path(__file__).resolve().parents[1]
RECTANGLE = (((0, 1), (3, 2, 4)), ((0, 1), (3, 4, 2)),
             ((1, 0), (3, 2, 4)), ((1, 0), (3, 4, 2)))


def reachable(start, graph):
    seen, pending = {start}, [start]
    while pending:
        for t in graph[pending.pop()]:
            if t not in seen:
                seen.add(t)
                pending.append(t)
    return seen


def verify_certificate(data):
    states = {(p[:k], p[k:]) for p in permutations(range(5)) for k in range(6)}
    trap = {s for s in states if balanced(s)}
    support = {(s, b) for s in trap for b in (0, 1)}
    check(len(trap) == 180 and len(support) == 360, 'support counts')
    check(data['switch_rate'] == 1, 'switching rate differs from the model')
    weights = {}
    for row in data['states']:
        state = (tuple(map(tuple, row['state'])), row['mode'])
        check(type(row['mode']) is int and row['mode'] in (0, 1), 'invalid mode')
        check(state not in weights, 'duplicate certificate state')
        check(type(row['weight']) is int and row['weight'] > 0, 'invalid weight')
        weights[state] = row['weight']
    check(set(weights) == support, 'incomplete certificate support')
    total = sum(weights.values())
    check(total == data['total_weight'], 'certificate total')
    residual = {s: 0 for s in support}
    # At unit position rates, 5! times the canonical weight is binomial(5, |c|).
    # Check both fixed-mode generators and their joint modulation on the same
    # operational event graph used for the distinguished-rate certificate.
    unit_weights = {(s, b): comb(5, len(s[0])) for s, b in support}
    unit_residual = {s: 0 for s in support}
    unit_queue_residual = {s: 0 for s in support}
    graph = {s: [] for s in support}
    reverse = {s: [] for s in support}
    count = 0
    for state in support:
        s, b = state
        limit = 2 if b == 0 else None
        events = [((s, 1 - b), 1)]
        for side in (0, 1):
            for pos, job in enumerate(s[side]):
                check(complete(s[side], pos, limit) == complete_carried(s[side], pos, limit),
                      'transition implementations disagree')
                if b == 1:
                    check(complete(s[side], pos, None) == complete(s[side], pos, 5),
                          'finite representation of unlimited mode differs')
                events.append(((transition(s, side, pos, limit), b), 2 if job == 0 else 1))
        check(sum(rate for _, rate in events) == 7, 'total exit rate')
        for target, rate in events:
            check(target in support, 'escape from joint support')
            check(target != state, 'unexpected self-event')
            residual[state] -= weights[state] * rate
            residual[target] += weights[state] * rate
            unit_residual[state] -= unit_weights[state]
            unit_residual[target] += unit_weights[state]
            if target[1] == b:
                unit_queue_residual[state] -= unit_weights[state]
                unit_queue_residual[target] += unit_weights[state]
            graph[state].append(target)
            reverse[target].append(state)
            count += 1
    check(not any(residual.values()), 'stationary balance failed')
    check(not any(unit_queue_residual.values()), 'unit-rate fixed-mode canonical balance')
    check(not any(unit_residual.values()), 'unit-rate modulated canonical balance')
    unit_mode_totals = [sum(v for (s, b), v in unit_weights.items() if b == mode)
                        for mode in (0, 1)]
    check(unit_mode_totals == [960, 960], 'unit-rate canonical normalizers')
    start = (RECTANGLE[0], 0)
    check(reachable(start, graph) == support and reachable(start, reverse) == support,
          'joint chain is not irreducible')
    mode_totals = [sum(v for (s, b), v in weights.items() if b == mode) for mode in (0, 1)]
    check(mode_totals == [total // 2] * 2 and total % 2 == 0, 'environment marginal')
    values = [weights[(s, 0)] for s in RECTANGLE]
    a, b, c, d = values
    determinant = a * d - b * c
    check(determinant % 101 == 85, 'limited-mode rectangle determinant')
    return {'status': 'PASS', 'states': 360, 'events': count,
            'budgets': [2, 'unlimited'], 'switch_rates': [1, 1],
            'class_rates': [2, 1, 1, 1, 1], 'total_exit_rate': 7,
            'closed_irreducible': True, 'integer_balance': 'PASS',
            'total_weight': total, 'mode_weights': mode_totals,
            'rectangle_mode': 0, 'rectangle_states': RECTANGLE,
            'rectangle_weights': values, 'rectangle_mod_101': [v % 101 for v in values],
            'determinant': determinant, 'determinant_mod_101': determinant % 101,
            'mode_dependent_queue_factorization_impossible': True,
            'unit_rate_comparison': {
                'class_rates': [1, 1, 1, 1, 1],
                'fixed_mode_canonical_balance': ['PASS', 'PASS'],
                'joint_canonical_balance': 'PASS',
                'integer_mode_weights': unit_mode_totals,
                'integer_total_weight': sum(unit_mode_totals),
                'canonical_queue_normalizer': 8,
                'stationary_law': '1 / (16 * |c|! * |d|!)',
                'queue_and_mode_independent': True}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', type=Path, default=ROOT/'data/modulated_certificate.json')
    args = parser.parse_args()
    print(json.dumps(verify_certificate(json.loads(args.certificate.read_text())), indent=2))


if __name__ == '__main__':
    main()
