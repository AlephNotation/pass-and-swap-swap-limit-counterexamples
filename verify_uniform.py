#!/usr/bin/env python3
"""Exact finite checks for the uniform odd-cycle product-form obstruction.

Python 3.10+, standard library only. Run: python3 verify_uniform.py
No network, simulation, floating point, external data, or output files are used.
The proof for every w is in uniform_note.pdf; finite enumeration is supplementary.
All checks remain active with python3 -O.
"""
from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction
from itertools import combinations, permutations
from math import comb, factorial
from typing import Iterable

Queue = tuple[int, ...]
State = tuple[Queue, Queue]
Orientation = tuple[bool, ...]
PARAMETERS = (Fraction(1, 2), Fraction(1), Fraction(2), Fraction(3))


class VerificationError(Exception):
    """An explicit verification condition failed."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise VerificationError(message)


def adjacent(a: int, b: int, n: int) -> bool:
    return (a - b) % n in (1, n - 1)


def complete(q: Queue, pos: int, limit: int | None, n: int) -> tuple[Queue, int, int]:
    """Find the replacement chain in the original queue, then apply it."""
    require(0 <= pos < len(q), "invalid completing position")
    chain = [pos]
    while limit is None or len(chain) - 1 < limit:
        i = chain[-1]
        j = next((j for j in range(i + 1, len(q)) if adjacent(q[i], q[j], n)), None)
        if j is None:
            break
        chain.append(j)
    result = list(q)
    for i, j in zip(chain, chain[1:]):
        result[j] = q[i]
    del result[pos]
    return tuple(result), q[chain[-1]], len(chain) - 1


def complete_carried(q: Queue, pos: int, limit: int | None, n: int) -> tuple[Queue, int, int]:
    """Internal cross-check: carry displaced jobs through a mutable queue."""
    result = list(q)
    carried = result.pop(pos)
    cursor, swaps = pos, 0
    while limit is None or swaps < limit:
        j = next((j for j in range(cursor, len(result))
                  if adjacent(carried, result[j], n)), None)
        if j is None:
            break
        result[j], carried = carried, result[j]
        cursor, swaps = j + 1, swaps + 1
    return tuple(result), carried, swaps


def destination(s: State, side: int, result: tuple[Queue, int, int]) -> State:
    q, departed, _ = result
    return (q, s[1] + (departed,)) if side == 0 else (s[0] + (departed,), q)


def transition(s: State, side: int, pos: int, limit: int | None, n: int) -> State:
    return destination(s, side, complete(s[side], pos, limit, n))


def orientation(s: State, n: int) -> Orientation:
    rank = {x: i for i, x in enumerate(s[0] + s[1][::-1])}
    return tuple(rank[i] < rank[(i + 1) % n] for i in range(n))


def height(s: State, n: int) -> int:
    distance: dict[int, int] = {}
    for x in s[0] + s[1][::-1]:
        distance[x] = 1 + max((distance[y] for y in ((x - 1) % n, (x + 1) % n)
                               if y in distance), default=-1)
    return max(distance.values())


def canonical_extension(w: int, u: int, direction: int) -> Queue:
    """A linear extension that puts the long-branch internal vertices first."""
    n = 2 * w + 1
    return ((u,) + tuple((u + direction * j) % n for j in range(1, w + 1))
            + tuple((u - direction * j) % n for j in range(1, w))
            + ((u + direction * (w + 1)) % n,))


def orientation_key(w: int, u: int, direction: int) -> Orientation:
    return orientation((canonical_extension(w, u, direction), ()), 2 * w + 1)


def balanced_states(w: int) -> set[State]:
    n = 2 * w + 1
    states: set[State] = set()
    for u in range(n):
        for direction in (-1, 1):
            a = tuple((u + direction * j) % n for j in range(1, w + 1))
            b = tuple((u - direction * j) % n for j in range(1, w))
            sink = (u + direction * (w + 1)) % n
            for chosen in combinations(range(n - 2), w):
                chosen_set = set(chosen)
                ia = ib = 0
                middle = []
                for j in range(n - 2):
                    if j in chosen_set:
                        middle.append(a[ia]); ia += 1
                    else:
                        middle.append(b[ib]); ib += 1
                linear = (u, *middle, sink)
                for cut in range(n + 1):
                    s = (linear[:cut], linear[cut:][::-1])
                    require(s not in states, "duplicate balanced state")
                    states.add(s)
    require(len(states) == 2 * n * (n + 1) * comb(n - 2, w), "cardinality formula")
    return states


def special_states(w: int) -> tuple[State, State, State, State]:
    d = tuple(range(w, 0, -1)) + tuple(range(w + 1, 2 * w + 1))
    x = tuple(range(w, -1, -1)) + tuple(range(w + 1, 2 * w + 1))
    y = ((w, w + 1) + tuple(range(w - 1, 0, -1))
         + tuple(range(w + 2, 2 * w + 1)) + (0,))
    s = ((0,), d)
    other = ((2 * w,), d[:-1] + (0,))
    return s, ((), x), ((), y), other


def weight(s: State, theta: Fraction) -> Fraction:
    value = Fraction(1)
    for q in s:
        total = Fraction(0)
        for x in q:
            total += theta if x == 0 else 1
            value /= total
    return value


def residual_formula(w: int, theta: Fraction) -> Fraction:
    first = Fraction(1, factorial(w))
    for k in range(w, 2 * w + 1):
        first /= theta + k
    return first - Fraction(1, factorial(2 * w)) / (theta + 2 * w)


def reachable(start: State, graph: dict[State, list[State]]) -> set[State]:
    seen, stack = {start}, [start]
    while stack:
        for target in graph[stack.pop()]:
            if target not in seen:
                seen.add(target)
                stack.append(target)
    return seen


def check_generator_moves(w: int, sources: Iterable[int]) -> int:
    n = 2 * w + 1
    checked = 0
    for u in sources:
        for direction in (-1, 1):
            a = (canonical_extension(w, u, direction), ())
            sink_flip = transition(a, 0, 0, w, n)
            require(orientation(sink_flip, n) == orientation_key(w, u, -direction),
                    "sink-flip orientation generator")
            v = (u + direction * (w + 1)) % n
            b = ((), canonical_extension(w, v, -direction))
            require(orientation(b, n) == orientation_key(w, u, direction),
                    "source-flip starting orientation")
            source_flip = transition(b, 1, 0, w, n)
            require(orientation(source_flip, n) == orientation_key(w, (u + direction) % n, -direction),
                    "source-flip orientation generator")
            checked += 2
    return checked


def check_words(w: int) -> None:
    n = 2 * w + 1
    s, x, y, other = special_states(w)
    require(transition(x, 1, 0, w, n) == s, "X limited destination")
    require(transition(x, 1, 0, None, n) == other, "X unlimited destination")
    require(transition(y, 1, 0, w, n) == other, "Y limited destination")
    require(transition(y, 1, 0, None, n) == s, "Y unlimited destination")
    for theta in PARAMETERS:
        defect = weight(x, theta) - weight(y, theta)
        require(defect == residual_formula(w, theta), "word weight formula")
        require((defect > 0) == (theta < 1) and (defect < 0) == (theta > 1),
                "defect sign")
        if theta == 2:
            require(defect == Fraction(-w, factorial(2 * w + 2)), "factorial simplification")


def check_balanced_region(w: int) -> dict:
    n = 2 * w + 1
    states = balanced_states(w)
    target, x, y, _ = special_states(w)
    require({target, x, y} <= states, "special states not balanced")
    keys = {s: orientation(s, n) for s in states}
    require(all(height(s, n) == w + 1 for s in states), "balanced height")
    weights = {theta: {s: weight(s, theta) for s in states} for theta in PARAMETERS}
    limited = {theta: dict.fromkeys(states, Fraction(0)) for theta in PARAMETERS}
    unlimited = {theta: dict.fromkeys(states, Fraction(0)) for theta in PARAMETERS}
    graph: dict[State, list[State]] = {s: [] for s in states}
    reverse: dict[State, list[State]] = {s: [] for s in states}
    zero: dict[State, list[State]] = {s: [] for s in states}
    zero_reverse: dict[State, list[State]] = {s: [] for s in states}
    added, removed = set(), set()
    changes = comparisons = events = 0
    for s in states:
        for side in (0, 1):
            for pos in range(len(s[side])):
                lw = complete(s[side], pos, w, n)
                li = complete(s[side], pos, None, n)
                require(lw == complete_carried(s[side], pos, w, n), "limited implementations disagree")
                require(li == complete_carried(s[side], pos, None, n), "unlimited implementations disagree")
                comparisons += 2
                events += 1
                t, u = destination(s, side, lw), destination(s, side, li)
                require(t in states and u in states, "balanced region not closed")
                require(keys[s] == keys[u], "unlimited orientation changed")
                graph[s].append(t); reverse[t].append(s)
                if lw[2] == 0:
                    require(keys[s] == keys[t], "zero-swap orientation changed")
                    zero[s].append(t); zero_reverse[t].append(s)
                if t != u:
                    changes += 1
                    require(pos == 0 and len(s[side]) == n and li[2] == w + 1,
                            "unexpected changed event")
                    if t == target:
                        added.add((s, side, pos))
                    if u == target:
                        removed.add((s, side, pos))
                for theta in PARAMETERS:
                    # The event rate is the INITIATING job's rate.
                    flow = weights[theta][s] * (theta if s[side][pos] == 0 else 1)
                    limited[theta][s] -= flow; limited[theta][t] += flow
                    unlimited[theta][s] -= flow; unlimited[theta][u] += flow
    require(added == {(x, 1, 0)} and removed == {(y, 1, 0)}, "two-flow completeness")
    require(reachable(target, graph) == states and reachable(target, reverse) == states,
            "all-position strong connectivity")
    fibres: dict[Orientation, set[State]] = {}
    for s, key in keys.items():
        fibres.setdefault(key, set()).add(s)
    require(len(fibres) == 2 * n, "number of balanced orientations")
    for fibre in fibres.values():
        representative = next(iter(fibre))
        require(reachable(representative, zero) == fibre and
                reachable(representative, zero_reverse) == fibre,
                "zero-swap fibre connectivity")
    values = {}
    for theta in PARAMETERS:
        require(not any(unlimited[theta].values()), "unlimited product-form control")
        defect = limited[theta][target]
        require(defect == residual_formula(w, theta), "full balance differs from formula")
        if theta == 1:
            require(not any(limited[theta].values()), "symmetric-rate finite control")
        values[str(theta)] = str(defect)
    return {
        "w": w, "vertices": n, "balanced_states": len(states),
        "position_events": events, "internal_implementation_comparisons": comparisons,
        "changed_events": changes, "balanced_orientations": len(fibres),
        "all_position_closure": "PASS", "zero_swap_fibre_connectivity": "PASS",
        "all_position_strong_connectivity": "PASS",
        "orientation_generator_moves": check_generator_moves(w, range(n)),
        "only_changed_incoming_events": "X at the second-queue head gained; Y at that head lost",
        "unlimited_product_form_control": "PASS", "symmetric_rate_control": "PASS",
        "target_residuals": values, "rate_two_factorial_formula": str(Fraction(-w, factorial(2 * w + 2))),
    }


def check_full_space(w: int) -> dict:
    """A separate completeness audit, not restricted to the proposed closed region."""
    n = 2 * w + 1
    target, x, y, _ = special_states(w)
    count = events = predecessors = 0
    added, removed = set(), set()
    for linear in permutations(range(n)):
        for cut in range(n + 1):
            s = (linear[:cut], linear[cut:][::-1])
            count += 1
            for side in (0, 1):
                for pos in range(len(s[side])):
                    t = transition(s, side, pos, w, n)
                    u = transition(s, side, pos, None, n)
                    events += 1
                    predecessors += t == target
                    if t != u:
                        if t == target:
                            added.add((s, side, pos))
                        if u == target:
                            removed.add((s, side, pos))
    require(added == {(x, 1, 0)} and removed == {(y, 1, 0)}, "full-space changed incoming events")
    return {"w": w, "full_states": count, "position_events": events,
            "limited_predecessor_events": predecessors, "two_changed_incoming_events": "PASS"}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--max-w", type=int, default=5,
                        help="enumerate complete balanced regions for 2 <= w <= this value (2..6; default 5)")
    parser.add_argument("--word-max-w", type=int, default=50,
                        help="check the two explicit words and generator moves through this w (default 50)")
    parser.add_argument("--full-space-max-w", type=int, choices=(2, 3), default=3,
                        help="also audit the full factorial state space through w=2 or 3 (default 3)")
    args = parser.parse_args()
    if not 2 <= args.max_w <= 6 or not args.max_w <= args.word_max_w <= 200:
        parser.error("require 2 <= max-w <= 6 and max-w <= word-max-w <= 200")
    try:
        regions = []
        for w in range(2, args.max_w + 1):
            print(f"Checking the complete balanced region at w={w} ...", file=sys.stderr, flush=True)
            regions.append(check_balanced_region(w))
        for w in range(2, args.word_max_w + 1):
            check_words(w)
            check_generator_moves(w, (0,))
        full_space = [check_full_space(w) for w in range(2, args.full_space_max_w + 1)]
        results = {
            "status": "PASS", "arithmetic": "exact integers and fractions",
            "scope": "Finite checks supplement the all-w written proof; they are not independent review.",
            "balanced_region_checks": regions,
            "full_space_completeness_audits": full_space,
            "explicit_word_checks": {"first_w": 2, "last_w": args.word_max_w,
                                     "parameters": list(map(str, PARAMETERS)),
                                     "four_transition_identities": "PASS",
                                     "factorial_formula_at_rate_two": "PASS"},
        }
        print(json.dumps(results, indent=2))
    except (VerificationError, ValueError, KeyError, TypeError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
