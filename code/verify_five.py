#!/usr/bin/env python3
"""Exact verifier for the accompanying compact pass-and-swap note.

Python 3.10+, standard library only. No network access, simulation, or floats.
Core: python3 verify.py
Complete: python3 verify.py --certificate stationary_certificate.json

A state is (c, d), both tuples in head-to-tail order. Positions are zero-based
inside this file; the note uses one-based positions. The rate of an event is
that of the INITIATING job, not necessarily that of the job that departs.
All checks remain active under python -O. Output is deterministic JSON.
"""
from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from fractions import Fraction
from itertools import permutations
from pathlib import Path

Queue = tuple[int, ...]
State = tuple[Queue, Queue]
Event = tuple[State, int, int]  # (destination, queue index, completing position)
EDGES = tuple((i, (i + 1) % 5) for i in range(5))
START: State = ((0, 1), (2, 3, 4))
TARGET: State = ((0,), (2, 1, 3, 4))


class VerificationError(Exception):
    """A claimed exact identity failed."""


def check(condition: bool, message: str) -> None:
    if not condition:
        raise VerificationError(message)


def adjacent(a: int, b: int) -> bool:
    return (a - b) % 5 in (1, 4)


def complete(q: Queue, pos: int, limit: int | None) -> tuple[Queue, int]:
    """Original-index implementation: find the successive replacement positions."""
    check(0 <= pos < len(q), "invalid completing position")
    chain = [pos]
    while limit is None or len(chain) - 1 < limit:
        i = chain[-1]
        j = next((j for j in range(i + 1, len(q))
                  if adjacent(q[i], q[j])), None)
        if j is None:
            break
        chain.append(j)
    result = list(q)
    for i, j in zip(chain, chain[1:]):
        result[j] = q[i]
    del result[pos]
    return tuple(result), q[chain[-1]]


def complete_carried(q: Queue, pos: int, limit: int | None) -> tuple[Queue, int]:
    """Internal cross-check: remove and carry the completing job through the queue."""
    result = list(q)
    carried = result.pop(pos)
    cursor, swaps = pos, 0
    while limit is None or swaps < limit:
        j = next((j for j in range(cursor, len(result))
                  if adjacent(carried, result[j])), None)
        if j is None:
            break
        result[j], carried = carried, result[j]
        cursor, swaps = j + 1, swaps + 1
    return tuple(result), carried


def transition(s: State, side: int, pos: int, limit: int | None) -> State:
    remaining, departed = complete(s[side], pos, limit)
    t = list(s)
    t[side] = remaining
    t[1 - side] = s[1 - side] + (departed,)
    return t[0], t[1]


def events(s: State, limit: int | None) -> list[Event]:
    return [(transition(s, side, pos, limit), side, pos)
            for side in (0, 1) for pos in range(len(s[side]))]


def orientation(s: State) -> tuple[tuple[int, int], ...]:
    rank = {x: i for i, x in enumerate(s[0] + s[1][::-1])}
    return tuple(sorted((a, b) if rank[a] < rank[b] else (b, a)
                        for a, b in EDGES))


def height(s: State) -> int:
    arcs = orientation(s)
    distance: dict[int, int] = {}
    for b in s[0] + s[1][::-1]:
        distance[b] = max([0] + [distance[a] + 1 for a, v in arcs if v == b])
    return max(distance.values())


def balanced(s: State) -> bool:
    """Exactly two directed source-to-sink branches, with lengths two and three."""
    arcs = set(orientation(s))
    for u in range(5):
        for direction in (-1, 1):
            long = tuple((u + direction * j) % 5 for j in range(4))
            short = tuple((u - direction * j) % 5 for j in range(3))
            expected = set(zip(long, long[1:])) | set(zip(short, short[1:]))
            if arcs == expected:
                return True
    return False


def reachable(start: State, graph: dict[State, list[State]]) -> set[State]:
    seen, pending = {start}, [start]
    while pending:
        for t in graph[pending.pop()]:
            if t not in seen:
                seen.add(t)
                pending.append(t)
    return seen


def event_rate(s: State, side: int, pos: int, theta: Fraction) -> Fraction:
    return theta if s[side][pos] == 0 else Fraction(1)


def weight(s: State, theta: Fraction) -> Fraction:
    answer = Fraction(1)
    for q in s:
        total = Fraction(0)
        for x in q:
            total += theta if x == 0 else 1
            answer /= total
    return answer


def residuals(support: set[State], limit: int | None,
              theta: Fraction) -> dict[State, Fraction]:
    out = {s: Fraction(0) for s in support}
    for s in support:
        for t, side, pos in events(s, limit):
            check(t in support, "control support is not closed")
            flow = weight(s, theta) * event_rate(s, side, pos, theta)
            out[s] -= flow
            out[t] += flow
    return out


def expanded_product(factors: tuple[tuple[int, int], ...]) -> list[int]:
    """Coefficients of a product of (constant + coefficient * theta) factors."""
    coefficients = [1]
    for a, b in factors:
        nxt = [0] * (len(coefficients) + 1)
        for i, c in enumerate(coefficients):
            nxt[i] += a * c
            nxt[i + 1] += b * c
        coefficients = nxt
    return coefficients


def verify_parameter_identity() -> None:
    # Multiply the claimed rational identity by
    # 24*theta*(theta+2)*(theta+3)*(theta+4), which is positive for theta>0.
    # These are the terms from incoming minus outgoing minus the claimed RHS.
    terms = (
        (4, ((2, 1), (3, 1), (4, 1))),
        (12, ((0, 1),)),
        (1, ((0, 1), (2, 1), (3, 1), (3, 1))),
        (-1, ((2, 1), (3, 1), (4, 1), (4, 1))),
        (1, ((0, 1), (-1, 1), (6, 1))),
    )
    coefficients: Counter[int] = Counter()
    for multiplier, factors in terms:
        for i, a in enumerate(expanded_product(factors)):
            coefficients[i] += multiplier * a
    check(all(a == 0 for a in coefficients.values()), "parameter identity failed")


def verify_certificate(path: Path, support: set[State],
                       graph: dict[State, list[Event]]) -> dict:
    data = json.loads(path.read_text(encoding="utf-8"))
    weights: dict[State, int] = {}
    for row in data["states"]:
        c, d = row["state"]
        s = (tuple(c), tuple(d))
        check(s not in weights, "duplicate certificate state")
        value = row["weight"]
        check(type(value) is int and value > 0, "nonpositive/noninteger weight")
        weights[s] = value
    check(set(weights) == support, "incorrect stationary-certificate support")
    check(sum(weights.values()) == data["total_weight"], "incorrect total weight")
    balance = {s: 0 for s in support}
    for s, value in weights.items():
        for t, side, pos in graph[s]:
            rate = 2 if s[side][pos] == 0 else 1
            balance[s] -= value * rate
            balance[t] += value * rate
    check(all(b == 0 for b in balance.values()), "integer stationary balance failed")
    cs, ds = ((0, 1), (1, 0)), ((3, 2, 4), (3, 4, 2))
    matrix = [[weights[(c, d)] for d in ds] for c in cs]
    determinant = matrix[0][0] * matrix[1][1] - matrix[0][1] * matrix[1][0]
    check(determinant % 101 == 52, "nonfactorization witness failed")
    return {"states": len(weights), "positive_integer_balance": "PASS",
            "total_weight": sum(weights.values()),
            "rectangle_mod_101": [[v % 101 for v in row] for row in matrix],
            "determinant_mod_101": determinant % 101}


def verify(certificate: Path | None) -> dict:
    states = [(p[:k], p[k:][::-1]) for p in permutations(range(5)) for k in range(6)]
    all_states = set(states)
    check(len(states) == len(all_states) == 720, "state enumeration failed")
    graph = {s: events(s, 2) for s in states}
    comparisons = 0
    for s in states:
        for limit in (2, None):
            for side in (0, 1):
                for pos in range(len(s[side])):
                    check(complete(s[side], pos, limit) ==
                          complete_carried(s[side], pos, limit), "transition disagreement")
                    comparisons += 1
                    t = transition(s, side, pos, limit)
                    check(t in all_states, "population not preserved")
                    if limit is None:
                        check(orientation(t) == orientation(s), "unlimited orientation changed")
    check(transition(((), (0, 1, 2, 4, 3)), 1, 0, 2) ==
          ((2,), (0, 1, 4, 3)), "displayed two-swap event failed")

    support = {s for s in states if balanced(s)}
    check(len(support) == 180 and START in support and TARGET in support, "balanced set failed")
    check(all(height(s) == 3 for s in support), "height-three condition failed")
    check(all(t in support for s in support for t, _, _ in graph[s]), "all-position escape")
    head = {s: [t for t, _, pos in graph[s] if pos == 0] for s in support}
    reverse: dict[State, list[State]] = {s: [] for s in support}
    for s in support:
        for t in head[s]:
            reverse[t].append(s)
    check(reachable(START, head) == support, "forward head reachability failed")
    check(reachable(START, reverse) == support, "reverse head reachability failed")
    check(all(len(head[s]) == len(reverse[s]) for s in support), "unit-head uniform balance")

    # Exhaustively derive all predecessor EVENTS, not only distinct predecessors.
    predecessors = {(s, side, pos) for s in states for t, side, pos in graph[s] if t == TARGET}
    expected = {
        (((0, 4), (2, 1, 3)), 0, 0), (((0, 4), (2, 1, 3)), 0, 1),
        (((), (2, 1, 0, 3, 4)), 1, 0),
        (((), (2, 1, 3, 4, 0)), 1, 2), (((), (2, 1, 3, 4, 0)), 1, 3),
        (((), (2, 1, 3, 4, 0)), 1, 4), (((), (2, 3, 1, 4, 0)), 1, 1),
    }
    check(predecessors == expected, "predecessor table is incomplete/incorrect")
    verify_parameter_identity()
    parameters = [Fraction(1, 3), Fraction(1, 2), Fraction(1),
                  Fraction(2), Fraction(3), Fraction(7, 2)]
    for theta in parameters:
        incoming = sum((weight(s, theta) * event_rate(s, side, pos, theta)
                        for s, side, pos in predecessors), Fraction(0))
        outgoing = weight(TARGET, theta) * (theta + 4)
        formula = -(theta - 1) * (theta + 6) / (24 * (theta + 2) * (theta + 3) * (theta + 4))
        check(incoming - outgoing == formula, "rational balance residual failed")
        # Under unlimited P&S the same weights must be stationary on this support.
        check(all(x == 0 for x in residuals(support, None, theta).values()),
              "unlimited positive control failed")
    check(all(x == 0 for x in residuals(support, 2, Fraction(1)).values()),
          "symmetric-rate positive control failed")

    # A fixed short-orientation control, chosen deterministically from the full state space.
    short_start = next(s for s in states if height(s) <= 2)
    short = {s for s in states if orientation(s) == orientation(short_start)}
    for theta in parameters:
        check(all(x == 0 for x in residuals(short, 2, theta).values()),
              "short-orientation positive control failed")
    incoming2 = sum((weight(s, Fraction(2)) * event_rate(s, side, pos, Fraction(2))
                     for s, side, pos in predecessors), Fraction(0))
    check(incoming2 == Fraction(11, 90), "rate-two inflow")
    check(weight(TARGET, Fraction(2)) * 6 == Fraction(1, 8), "rate-two outflow")

    results = {
        "status": "PASS",
        "full_states": 720,
        "limited_position_events": sum(len(v) for v in graph.values()),
        "two_implementations_compared_limited_and_unlimited": comparisons,
        "unlimited_orientation_checks": 3600,
        "balanced_states": len(support),
        "balanced_position_events": sum(len(graph[s]) for s in support),
        "balanced_heights": sorted({height(s) for s in support}),
        "head_strong_connectivity": "PASS",
        "unit_head_uniform_stationarity": "PASS",
        "predecessor_states": len({s for s, _, _ in predecessors}),
        "predecessor_events": len(predecessors),
        "rate_two_incoming_weighted_flow": str(incoming2),
        "rate_two_outgoing_weighted_flow": "1/8",
        "rate_two_residual": str(incoming2 - Fraction(1, 8)),
        "all_parameter_polynomial_identity": "PASS",
        "supplemental_rational_parameters": list(map(str, parameters)),
        "unlimited_product_form_control": "PASS",
        "symmetric_rate_product_form_control": "PASS",
        "short_orientation_control_states": len(short),
        "short_orientation_product_form_control": "PASS",
        "stationary_certificate": "not requested",
    }
    if certificate is not None:
        results["stationary_certificate"] = verify_certificate(certificate, support, graph)
    return results


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--certificate", type=Path,
                        help="also verify the supplied integer stationary law and nonfactorization")
    args = parser.parse_args()
    try:
        print(json.dumps(verify(args.certificate), indent=2))
    except (VerificationError, OSError, ValueError, KeyError, TypeError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
