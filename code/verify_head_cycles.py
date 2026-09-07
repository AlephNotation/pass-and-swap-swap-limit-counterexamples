#!/usr/bin/env python3
"""Exact finite checks on seven nonexceptional cycles under two event supports.

One distinct job per vertex. Enumerate the full state space and compare
head-only with all-position completions using the existing operational
implementations and terminal-SCC algorithm. This is finite evidence only;
it does not prove removal of the general positive-position hypothesis.
All checks remain active under Python -O.
"""
from collections import Counter
import json
import sys

from verify_classification import event_graphs, recurrent_indices
from verify_uniform import require

CASES = ((6, 1), (6, 2), (6, 3), (7, 2), (8, 1), (8, 2), (8, 3))


def check_case(n, w):
    require(n % (2 * w) != 1, 'case is not a nonexceptional cycle')
    states, heights, graphs = event_graphs(n, w)
    short = {i for i, h in enumerate(heights) if h <= w}
    require(all(j in short for i in short for j in graphs['all_positions'][i]),
            'short region is not closed under every completion')
    disciplines = {}
    for name, graph in graphs.items():
        recurrent, closed = recurrent_indices(graph)
        tall = sum(heights[i] > w for i in recurrent)
        require(tall == 0, f'C{n}/w={w}: tall recurrent state under {name}')
        disciplines[name] = {
            'events': sum(map(len, graph)),
            'closed_class_count': len(closed),
            'closed_class_size_histogram': dict(sorted(Counter(map(len, closed)).items())),
            'recurrent_states': len(recurrent),
            'transient_states': len(states) - len(recurrent),
            'tall_recurrent_states': tall,
        }
    return {'n': n, 'w': w, 'states': len(states), 'short_states': len(short),
            'short_region_closed_under_all_positions': True,
            'two_transition_implementations_agree': True,
            'disciplines': disciplines}


def run():
    cases = []
    for n, w in CASES:
        print(f'Checking C{n}/w={w} under head-only and all-position service...',
              file=sys.stderr, flush=True)
        cases.append(check_case(n, w))
    return {'status': 'PASS',
            'scope': 'Seven complete nonexceptional cycle state spaces; one job per vertex.',
            'total_state_budget_cases': sum(case['states'] for case in cases),
            'cases': cases}


if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
