#!/usr/bin/env python3
"""Exact C5 checks: canonical product form and queue-wise factorization.

Run with Python 3.10+; only the standard library is used. Every test remains
active with -O. The four-predecessor proof does not require a stationary
solver. An optional exact 45-orbit solver generates an additional certificate
ruling out arbitrary queue-wise factorization at rates (2,1,1,1,1).

  python code/regenerate_certificate.py --output regenerated_certificate.json
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import permutations
from math import gcd, lcm
from pathlib import Path
import argparse
import json

State = tuple[tuple[int, ...], tuple[int, ...]]
TARGET: State = ((0,), (2, 1, 3, 4))
RECTANGLE = (((0, 1), (3, 2, 4)), ((0, 1), (3, 4, 2)),
             ((1, 0), (3, 2, 4)), ((1, 0), (3, 4, 2)))


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def adjacent(a, b):
    return (a - b) % 5 in (1, 4)


def transition(state, side, pos, limit=2):
    q = list(state[side])
    carried = q.pop(pos)
    swaps = 0
    for j in range(pos, len(q)):
        if adjacent(carried, q[j]):
            carried, q[j] = q[j], carried
            swaps += 1
            if swaps == limit:
                break
    t = list(state)
    t[side] = tuple(q)
    t[1 - side] += (carried,)
    return tuple(t)


def actions(s):
    for side in (0, 1):
        for pos in range(len(s[side])):
            yield side, pos


def orientation(s):
    ranks = {x: i for i, x in enumerate(s[0] + s[1][::-1])}
    return tuple(ranks[i] < ranks[(i + 1) % 5] for i in range(5))


def height(s):
    depths = {}
    for x in s[0] + s[1][::-1]:
        depths[x] = max((depths[y] + 1 for y in depths if adjacent(x, y)), default=0)
    return max(depths.values())


STATES = tuple((p[:k], p[k:]) for p in permutations(range(5)) for k in range(6))
TRAP = tuple(s for s in STATES if height(s) == 3)
TRAP_SET = set(TRAP)


def canonical_weight(s, theta):
    out = F(1)
    for q in s:
        total = F(0)
        for x in q:
            total += theta if x == 0 else 1
            out /= total
    return out


def service_rate(s, side, pos, theta):
    return theta if s[side][pos] == 0 else F(1)


def residual(states, theta, limit=2):
    values = {s: canonical_weight(s, theta) for s in states}
    res = {s: F(0) for s in states}
    for s in states:
        for side, pos in actions(s):
            t = transition(s, side, pos, limit)
            require(t in res, 'test set is not closed')
            flux = values[s] * service_rate(s, side, pos, theta)
            res[s] -= flux
            res[t] += flux
    return res


def reachable(start, graph):
    seen, todo = {start}, [start]
    while todo:
        for t in graph[todo.pop()]:
            if t not in seen:
                seen.add(t)
                todo.append(t)
    return seen


def check_small_proof():
    require(len(STATES) == 720 and len(TRAP) == 180, 'state counts')
    head_edges = {s: [transition(s, i, 0) for i in (0, 1) if s[i]] for s in TRAP}
    reverse = {s: [] for s in TRAP}
    for s, targets in head_edges.items():
        for t in targets:
            require(t in TRAP_SET, 'head escape')
            reverse[t].append(s)
    require(reachable(TARGET, head_edges) == TRAP_SET, 'head connectivity')
    require(reachable(TARGET, reverse) == TRAP_SET, 'reverse head connectivity')

    expected = {
        ((0, 4), (2, 1, 3)): ((0, 0), (0, 1)),
        ((), (2, 1, 0, 3, 4)): ((1, 0),),
        ((), (2, 1, 3, 4, 0)): ((1, 2), (1, 3), (1, 4)),
        ((), (2, 3, 1, 4, 0)): ((1, 1),),
    }
    found = defaultdict(list)
    for s in STATES:
        for a in actions(s):
            if transition(s, *a) == TARGET:
                found[s].append(a)
    require(dict(found) == {s: list(a) for s, a in expected.items()}, 'predecessor table')
    table = []
    for s, acts in expected.items():
        weight = canonical_weight(s, F(2))
        rate = sum(service_rate(s, *a, F(2)) for a in acts)
        table.append(dict(state=s, positions=[(i, p + 1) for i, p in acts],
                          weight=str(weight), rate=str(rate), flux=str(weight * rate)))
    incoming = sum(F(row['flux']) for row in table)
    outgoing = canonical_weight(TARGET, F(2)) * 6
    require((incoming, outgoing) == (F(11, 90), F(1, 8)), 'explicit balance equation')

    short_seed = ((0, 2, 1, 4, 3), ())
    short = tuple(s for s in STATES if orientation(s) == orientation(short_seed))
    require(height(short_seed) == 2, 'short-order control height')
    tests = []
    for theta in map(F, ['1/3', '1/2', '1', '2', '3', '5']):
        res = residual(TRAP, theta)
        predicted = -(theta - 1) * (theta + 6) / (24 * (theta + 2) * (theta + 3) * (theta + 4))
        require(res[TARGET] == predicted, 'parameter formula check')
        require(not any(residual(TRAP, theta, 99).values()), 'unlimited control')
        require(not any(residual(short, theta).values()), 'Theorem 7 control')
        if theta == 1:
            require(not any(res.values()), 'symmetric unit-rate case')
        else:
            require(res[TARGET] != 0, 'asymmetric case should fail')
        tests.append(dict(theta=str(theta), target_residual=str(res[TARGET]),
                          nonzero_states=sum(bool(v) for v in res.values())))
    return dict(trap_states=len(TRAP), target=TARGET, predecessor_table=table,
                incoming=str(incoming), outgoing=str(outgoing), residual=str(incoming-outgoing),
                theta_checks=tests, short_control_states=len(short),
                unlimited_controls_pass=True, short_order_controls_pass=True)


def symmetry(s, eps, flip):
    t = tuple(tuple(eps * x % 5 for x in q) for q in s)
    return t[::-1] if flip else t


def canonical(s):
    return min(symmetry(s, eps, flip) for eps in (1, -1) for flip in (0, 1))


def solve_exact(matrix, rhs):
    """Exact Gaussian elimination, with explicit singularity checks."""
    n = len(rhs)
    a = [[F(x) for x in row] + [F(y)] for row, y in zip(matrix, rhs)]
    for col in range(n):
        pivot = next((i for i in range(col, n) if a[i][col]), None)
        require(pivot is not None, 'singular normalization system')
        a[col], a[pivot] = a[pivot], a[col]
        d = a[col][col]
        a[col][col:] = [x / d for x in a[col][col:]]
        for i in range(col + 1, n):
            f = a[i][col]
            if f:
                for j in range(col, n + 1):
                    a[i][j] -= f * a[col][j]
    sol = [F(0)] * n
    for i in range(n - 1, -1, -1):
        sol[i] = a[i][n] - sum(a[i][j] * sol[j] for j in range(i + 1, n))
    return sol


def make_certificate():
    reps = sorted({canonical(s) for s in TRAP})
    require(len(reps) == 45, 'remaining-symmetry quotient size')
    index = {s: i for i, s in enumerate(reps)}
    q = [[0] * len(reps) for _ in reps]
    for i, s in enumerate(reps):
        require(len({symmetry(s, e, f) for e in (1, -1) for f in (0, 1)}) == 4,
                'nonfree residual symmetry')
        for side, pos in actions(s):
            rate = int(service_rate(s, side, pos, F(2)))
            j = index[canonical(transition(s, side, pos))]
            q[i][j] += rate
            q[i][i] -= rate
    a = [list(row) for row in zip(*q)]
    a[-1] = [1] * len(reps)
    p = solve_exact(a, [0] * (len(reps)-1) + [1])
    pi = {s: p[index[canonical(s)]] / 4 for s in TRAP}
    require(sum(pi.values()) == 1 and all(v > 0 for v in pi.values()), 'normalization')
    denominator = lcm(*(v.denominator for v in pi.values()))
    weights = {s: int(v * denominator) for s, v in pi.items()}
    g = gcd(*weights.values())
    weights = {s: v // g for s, v in weights.items()}
    return dict(model='C5, w=2, per-job rates (2,1,1,1,1) in both queues',
                total_weight=sum(weights.values()),
                states=[dict(state=s, weight=v) for s, v in sorted(weights.items())])


def verify_certificate(cert):
    weights = {tuple(tuple(q) for q in row['state']): int(row['weight']) for row in cert['states']}
    require(len(cert['states']) == 180 and set(weights) == TRAP_SET, 'certificate state coverage')
    require(all(v > 0 for v in weights.values()), 'certificate positivity')
    require(sum(weights.values()) == cert['total_weight'], 'certificate normalization')
    res = {s: 0 for s in TRAP}
    for s in TRAP:
        for side, pos in actions(s):
            rate = int(service_rate(s, side, pos, F(2)))
            res[s] -= weights[s] * rate
            res[transition(s, side, pos)] += weights[s] * rate
    require(not any(res.values()), 'integer stationary balance')
    a, b, c, d = [weights[s] for s in RECTANGLE]
    determinant = a*d-b*c
    require(determinant != 0, 'no queue-factorization obstruction')
    return dict(integer_balance_verified_at_states=180,
                total_weight=sum(weights.values()), rectangle_states=RECTANGLE,
                rectangle_weights=[a, b, c, d], determinant=determinant,
                modulus=101, rectangle_weights_mod_101=[x % 101 for x in (a,b,c,d)],
                determinant_mod_101=determinant % 101,
                queue_wise_factorization_impossible=True)


def main():
    parser = argparse.ArgumentParser(description="Regenerate the exact stationary certificate using rational Gaussian elimination.")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    cert = make_certificate()
    result = verify_certificate(cert)
    args.output.write_text(json.dumps(cert, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
