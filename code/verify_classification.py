#!/usr/bin/env python3
"""Exact complete-state classification on C5 (w=2) and C7 (w=3).

Python 3.10+, standard library only. Uses an iterative SCC algorithm. This
checks both unit-head and unit-per-position event graphs; no stochastic
simulation or stationary linear solver is used. Assertions are not used.
"""
from __future__ import annotations
import json
import sys
from collections import Counter
from itertools import permutations
from verify_uniform import (balanced_states, complete_carried, destination,
                            height, require, transition)


def recurrent_indices(graph: list[list[int]]) -> tuple[set[int], list[list[int]]]:
    """Kosaraju's algorithm, followed by the terminal-component test."""
    n = len(graph)
    reverse = [[] for _ in graph]
    for u, targets in enumerate(graph):
        for v in targets:
            reverse[v].append(u)
    seen = bytearray(n)
    finish = []
    for root in range(n):
        if seen[root]:
            continue
        seen[root] = 1
        stack = [(root, 0)]
        while stack:
            u, k = stack[-1]
            if k == len(graph[u]):
                finish.append(u)
                stack.pop()
            else:
                stack[-1] = (u, k + 1)
                v = graph[u][k]
                if not seen[v]:
                    seen[v] = 1
                    stack.append((v, 0))
    owner = [-1] * n
    components = []
    for root in reversed(finish):
        if owner[root] != -1:
            continue
        number = len(components)
        owner[root] = number
        todo, members = [root], []
        while todo:
            u = todo.pop()
            members.append(u)
            for v in reverse[u]:
                if owner[v] == -1:
                    owner[v] = number
                    todo.append(v)
        components.append(members)
    terminal = [True] * len(components)
    for u, targets in enumerate(graph):
        for v in targets:
            if owner[u] != owner[v]:
                terminal[owner[u]] = False
    closed = [c for i, c in enumerate(components) if terminal[i]]
    return {u for c in closed for u in c}, closed


def check_case(w: int) -> dict:
    n = 2 * w + 1
    states = [(p[:k], p[k:][::-1]) for p in permutations(range(n))
              for k in range(n + 1)]
    index = {s: i for i, s in enumerate(states)}
    heights = [height(s, n) for s in states]
    balanced = {index[s] for s in balanced_states(w)}
    heads = [[] for _ in states]
    allpos = [[] for _ in states]
    for i, s in enumerate(states):
        for side in (0, 1):
            for p in range(len(s[side])):
                t = destination(s, side, complete_carried(s[side], p, w, n))
                require(t == transition(s, side, p, w, n), 'classification transition mismatch')
                j = index[t]
                allpos[i].append(j)
                if p == 0:
                    heads[i].append(j)
    disciplines = {}
    for name, graph in [('head_only', heads), ('all_positions', allpos)]:
        recurrent, closed = recurrent_indices(graph)
        tall_recurrent = {i for i in recurrent if heights[i] > w}
        require(tall_recurrent == balanced, f'w={w}: unexpected tall recurrent set ({name})')
        short = {i for i, h in enumerate(heights) if h <= w}
        require(short <= recurrent, 'short states unexpectedly transient')
        require(any(set(c) == balanced for c in closed), 'balanced set not a single closed class')
        disciplines[name] = {
            'events': sum(map(len, graph)),
            'recurrent_states': len(recurrent),
            'transient_states': len(states) - len(recurrent),
            'recurrent_by_height': dict(sorted(Counter(heights[i] for i in recurrent).items())),
            'transient_by_height': dict(sorted(Counter(heights[i] for i in range(len(states))
                                                         if i not in recurrent).items())),
            'closed_class_count': len(closed),
            'closed_class_size_histogram': dict(sorted(Counter(map(len, closed)).items())),
            'tall_recurrent_equals_balanced': True,
            'balanced_single_closed_class': True,
        }
    return {'w': w, 'vertices': n, 'full_states': len(states),
            'height_counts': dict(sorted(Counter(heights).items())),
            'balanced_states': len(balanced), 'disciplines': disciplines}


def run() -> dict:
    return {'status': 'PASS', 'scope': 'Complete state spaces, one distinct job per cycle vertex.',
            'cases': [check_case(w) for w in (2, 3)]}


if __name__ == '__main__':
    try:
        print(json.dumps(run(), indent=2))
    except (RuntimeError, ValueError) as exc:
        print(f'FAIL: {exc}', file=sys.stderr)
        raise SystemExit(1)
