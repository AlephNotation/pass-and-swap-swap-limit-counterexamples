#!/usr/bin/env python3
"""Reproduce the C9/w=2 exceptional-class check using exact integer flows.

This is a finite verification of a proved instance, not the family proof.
Scale canonical weights by 9!, giving binomial(9, len(c)). Python 3.10+,
standard library only; checks remain active under -O.
"""
from collections import Counter
from fractions import Fraction
from itertools import permutations
from math import comb, factorial
import json

from verify_uniform import complete, complete_carried, destination, orientation, require

N, W = 9, 2
TARGET = ((0,), (7, 8, 6, 3, 4, 5, 2, 1))
GAINED = ((), (7, 8, 0, 6, 3, 4, 5, 2, 1))
LOST = [
    ((3, 7, 8, 6, 2, 4, 5, 1, 0), 1),
    ((7, 3, 8, 6, 2, 4, 5, 1, 0), 2),
    ((7, 8, 3, 6, 2, 4, 5, 1, 0), 3),
    ((7, 8, 6, 3, 2, 4, 5, 1, 0), 4),
]


def runs(bits):
    start = next(i for i in range(N) if bits[i] != bits[i - 1])
    lengths = [1]
    for j in range(1, N):
        if bits[(start + j) % N] == bits[(start + j - 1) % N]:
            lengths[-1] += 1
        else:
            lengths.append(1)
    return lengths


def run():
    states = []
    orientations = set()
    for word in permutations(range(N)):
        bits = orientation((word, ()), N)
        if sorted(runs(bits)) == [2, 2, 2, 3]:
            orientations.add(bits)
            states.extend((word[:j], word[j:][::-1]) for j in range(N + 1))
    index = {s: i for i, s in enumerate(states)}
    require(len(states) == len(index) == 131040, 'C9 support count')
    require(len(orientations) == 18, 'C9 orientation count')
    require(TARGET in index, 'target membership')
    limited = [0] * len(states)
    unlimited = [0] * len(states)
    gained, lost = [], []
    events = 0
    for i, s in enumerate(states):
        weight = comb(N, len(s[0]))
        for side in (0, 1):
            for pos in range(len(s[side])):
                results = []
                for budget, residual in ((W, limited), (None, unlimited)):
                    result = complete(s[side], pos, budget, N)
                    require(result == complete_carried(s[side], pos, budget, N),
                            'independent transition implementation mismatch')
                    t = destination(s, side, result)
                    require(t in index, 'exceptional support is not closed')
                    residual[i] -= weight
                    residual[index[t]] += weight
                    results.append(t)
                if results[0] != results[1]:
                    event = (s, side, pos + 1)
                    if results[0] == TARGET:
                        gained.append(event)
                    if results[1] == TARGET:
                        lost.append(event)
                events += 1
    require(events == 1179360, 'C9 event count per generator')
    require(all(x == 0 for x in unlimited), 'unlimited canonical balance')
    require(sum(x != 0 for x in limited) == 16560, 'limited residual count')
    require(limited[index[TARGET]] == -3, 'target integer residual')
    require(gained == [(GAINED, 1, 1)], 'complete gained predecessor list')
    require(sorted(lost) == sorted((((), q), 1, p) for q, p in LOST),
            'complete lost predecessor list')
    by_length = Counter()
    for s, residual in zip(states, limited):
        by_length[len(s[0])] += residual
    require(all(x == 0 for x in by_length.values()), 'length residual cancellation')
    return {
        'status': 'PASS', 'n': N, 'w': W,
        'scope': 'Entire exceptional class; unit rate at every occupied position.',
        'states': len(states), 'orientations': len(orientations),
        'events_per_generator': events,
        'integer_weight': 'binomial(9, len(c)) = 9! W(c,d)',
        'unlimited_nonzero_residuals': 0,
        'limited_nonzero_residuals': sum(x != 0 for x in limited),
        'target': TARGET, 'target_integer_residual': limited[index[TARGET]],
        'target_unnormalized_residual': str(Fraction(limited[index[TARGET]], factorial(N))),
        'gained_events': gained, 'lost_events': sorted(lost),
        'length_residuals': [by_length[j] for j in range(N + 1)],
        'closed_under_both_generators': True,
        'two_transition_implementations_agree': True,
    }


if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
