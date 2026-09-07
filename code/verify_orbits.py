#!/usr/bin/env python3
"""Exact standard-library check of the C5, w=2 counterexample.

Run: python3 code/verify_orbits.py
Tests remain active with python -O. No simulation or floating-point arithmetic.
Every position is tested, even if its service rate could be zero in a specific
allocation. Actual OI transitions are a subset; both head transitions are
always present by Definition 1 of Dorsman and Gardner (2024).
"""
from collections import Counter
from itertools import permutations
from pathlib import Path
import json

REPS = (
    ((), (0, 1, 2, 4, 3)),
    ((), (0, 1, 4, 2, 3)),
    ((), (0, 1, 4, 3, 2)),
    ((0,), (2, 1, 3, 4)),
    ((0,), (2, 3, 1, 4)),
    ((0,), (2, 3, 4, 1)),
    ((0, 1), (2, 3, 4)),
    ((0, 1), (3, 2, 4)),
    ((0, 1), (3, 4, 2)),
)
GROUP = tuple((eps, k, flip) for eps in (1, -1)
              for k in range(5) for flip in (0, 1))


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def adjacent(x, y):
    return (x - y) % 5 in (1, 4)


def serve_carry(queue, position):
    """Remove the completing job, then carry it through later positions."""
    rest = list(queue)
    carried = rest.pop(position)
    swaps = 0
    for j in range(position, len(rest)):
        if adjacent(carried, rest[j]):
            carried, rest[j] = rest[j], carried
            swaps += 1
            if swaps == 2:
                break
    return tuple(rest), carried


def serve_indices(queue, position):
    """Compute replacement indices first in the UNMODIFIED original queue."""
    chain = [position]
    for _ in range(2):
        last = chain[-1]
        candidates = [j for j in range(last + 1, len(queue))
                      if adjacent(queue[last], queue[j])]
        if not candidates:
            break
        chain.append(candidates[0])
    replacements = {chain[j]: queue[chain[j - 1]]
                    for j in range(1, len(chain))}
    new_queue = tuple(replacements.get(j, x)
                      for j, x in enumerate(queue) if j != position)
    return new_queue, queue[chain[-1]]


def transition(state, side, position, serve=serve_carry):
    q = list(state)
    q[side], job = serve(q[side], position)
    q[1 - side] += (job,)
    return tuple(q)


def actions(state, heads_only=False):
    for side in (0, 1):
        positions = range(min(1, len(state[side]))) if heads_only else range(len(state[side]))
        for position in positions:
            yield side, position


def transform(state, group):
    eps, k, flip = group
    result = tuple(tuple((eps * x + k) % 5 for x in q) for q in state)
    return result[::-1] if flip else result


def height(state):
    depth = {}
    for x in state[0] + state[1][::-1]:
        depth[x] = max((depth[y] + 1 for y in depth if adjacent(x, y)), default=0)
    return max(depth.values())


def reachable(start, edges):
    seen, pending = {start}, [start]
    while pending:
        state = pending.pop()
        for target in edges[state]:
            if target not in seen:
                seen.add(target)
                pending.append(target)
    return seen


def check():
    states = tuple((p[:k], p[k:]) for p in permutations(range(5)) for k in range(6))
    orbits = tuple({transform(s, g) for g in GROUP} for s in REPS)
    owner = {}
    for i, orbit in enumerate(orbits, 1):
        require(len(orbit) == 20, 'non-free symmetry action')
        for s in orbit:
            require(s not in owner, 'overlapping orbits')
            owner[s] = i
    trap = set(owner)
    require(len(trap) == 180, 'wrong trap size')
    require(trap == {s for s in states if height(s) == 3}, 'trap is not exactly height-three states')

    comparisons = equivariance = 0
    for s in states:
        for side, pos in actions(s):
            target = transition(s, side, pos)
            require(target == transition(s, side, pos, serve_indices), 'transition implementations disagree')
            comparisons += 1
            for g in GROUP:
                require(transform(target, g) == transition(transform(s, g), side ^ g[2], pos), 'equivariance failed')
                equivariance += 1

    head_edges = {}
    all_edges = {}
    for s in trap:
        all_edges[s] = tuple(transition(s, side, p) for side, p in actions(s))
        require(all(t in trap for t in all_edges[s]), 'all-position closure failed')
        head_edges[s] = tuple(transition(s, side, p) for side, p in actions(s, True))
    reverse = {s: [] for s in trap}
    for s, targets in head_edges.items():
        for t in targets:
            reverse[t].append(s)
    require(reachable(REPS[6], head_edges) == trap, 'not all states reachable by heads')
    require(reachable(REPS[6], reverse) == trap, 'not all states return by heads')
    head_in = Counter(t for targets in head_edges.values() for t in targets)
    require(all(head_in[s] == len(head_edges[s]) for s in trap), 'head-only uniform stationarity failed')
    all_in = Counter(t for targets in all_edges.values() for t in targets)

    certificate = []
    for i, s in enumerate(REPS, 1):
        for side, pos in actions(s):
            t = transition(s, side, pos)
            j = owner[t]
            witnesses = [g for g in GROUP if transform(REPS[j - 1], g) == t]
            require(len(witnesses) == 1, 'symmetry witness not unique')
            certificate.append(dict(source_orbit=i, queue='C' if side == 0 else 'D',
                                    position=pos + 1, target=t, target_orbit=j,
                                    symmetry=witnesses[0]))
    # Two explicitly checked paths lift to generators of the full symmetry group.
    # CCDD reaches a(s7), where a is reflection x -> 4-x.
    # CDD reaches b(s7), where b is reflection x -> 2-x plus queue exchange.
    # a*b = rotation by 2 plus exchange; its order is ten. Together a,b
    # generate all 20 graph-and-queue symmetries.
    for word, group in [('CCDD', (-1, 4, 0)), ('CDD', (-1, 2, 1))]:
        state = REPS[6]
        for letter in word:
            state = transition(state, 0 if letter == 'C' else 1, 0)
        require(state == transform(REPS[6], group), 'generator path failed')

    summary = dict(status='PASS', full_states=len(states), full_height_counts=dict(sorted(Counter(map(height, states)).items())),
                   transition_comparisons=comparisons, equivariance_checks=equivariance,
                   orbit_count=len(orbits), orbit_sizes=[len(o) for o in orbits],
                   trap_states=len(trap), all_position_transitions_in_trap=sum(map(len, all_edges.values())),
                   representative_all_position_cases=len(certificate),
                   head_transitions_in_trap=sum(map(len, head_edges.values())),
                   head_graph_strongly_connected=True, all_position_closure=True,
                   unit_head_uniform_stationary=True,
                   unit_per_position_uniform_stationary=all(all_in[s] == 5 for s in trap),
                   all_position_incoming_counts_by_orbit=[all_in[s] for s in REPS])
    here = Path(__file__).resolve().parents[1]
    supplied = json.loads((here / 'data/all_position_certificate.json').read_text())
    require(supplied == json.loads(json.dumps(certificate)), 'stored orbit certificate mismatch')
    print(json.dumps(summary, indent=2))
    return trap, head_edges, all_edges, owner


if __name__ == '__main__':
    check()
