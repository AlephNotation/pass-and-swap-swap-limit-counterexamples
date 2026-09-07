# Review of research_ladder

Reviewed 7 September 2026. Source folder:
`/Users/tynandaly/Downloads/research_ladder`.

The supplied slow-mixing argument is sound under its stated assumptions. Its
arbitrary-size mixing estimates are new relative to the current Lean development;
this review and the improvement below are mathematical arguments, not Lean proofs.
The two supplied finite screens concern results already covered by the cycle
classification formalization.

Subsequent work is tracked in [STRUCTURAL_THEORY.md](STRUCTURAL_THEORY.md).
It formalizes the length-generator identities and finite-kernel and
Poisson-averaged flow bounds, and develops the canonical-marginal consequence.
The full continuous-time mixing theorem still has the obligations listed there.

## Checks reproduced

Both scripts were imported and their functions rerun, without overwriting the
supplied JSON files. Every regenerated record matched its supplied record.

| Check | Range | Coverage | Result |
|---|---|---:|---|
| Terminal orientation components | `3 ≤ n ≤ 14`, `1 ≤ w < n` | 90 pairs; 393,036 orientation states | Exact JSON match |
| Operational orientation quotient | `3 ≤ n ≤ 7`, `1 ≤ w < n` | 20 pairs; 1,860,624 completion events | Exact JSON match |

I also enumerated the balanced classes for `(n,w)=(5,2),(7,3),(9,4),(11,5)`:
40,864 states and 431,344 events. These checks used both the downloaded transition
implementation and the repository's independently implemented replacement-chain
routine, and verified that:

- Every destination stays in the balanced class.
- The rates of changing `K=|c|` down and up are respectively `K` and `n-K`.
- Every orientation-changing event completes the head of a queue containing all
  `n` jobs. Each state has at most one such event.
- The nontrivial orientation graph is the bidirectional cycle on `2n` vertices.
- Label rotation and reflection preserve the balanced support and `K`, and give
  well-defined bijections on orientations.

These finite checks corroborate the structural claims; they do not establish
arbitrary-size mixing estimates.

## Review of the supplied proof

Assume `n=2w+1 ≥ 5`, restrict to `B_w`, and give each occupied position rate one.
Write `Q` for the continuous-time generator and `π` for its unique stationary law.
The total event rate is `n`. All time estimates below use these physical rates.

1. **Queue-length projection.** Every completion in the first queue reduces `K`
   by one, while every completion in the second increases it by one. Thus the
   projected generator has rates `k` and `n-k`. Its binomial stationary law follows
   from `binom(n,k)(n-k)=binom(n,k+1)(k+1)`. Independent rate-two fair bit refreshes
   give a coupling with failure probability at most `n exp(-2t)`. Consequently,
   `t_mix(K,1/4) ≤ (1/2) log(4n)`.

2. **Rare orientation changes.** The precise existing Lean input is
   `balanced_changed_event_head` in `OddCycle/ChangedEvents.lean`, combined with
   preservation of orientation under an unlimited budget. An orientation change
   must differ from the unlimited event, so it requires a head completion with
   the other queue empty. For its total rate `g`, this gives
   `g(x) ≤ 1_{K(x)∈{0,n}}` and `π(g) ≤ 2^(1-n)`.

3. **Conditional orientation symmetry.** Rotating or reflecting labels preserves
   adjacency, the first-later-compatible rule, event multiplicities, and unit
   service rates. It therefore commutes with the generator. Uniqueness of `π`
   gives invariance under these transformations. The dihedral action is transitive
   on balanced orientations and preserves `K`, so orientation is uniform on its
   `2n` values conditional on every `K=k`.

4. **A stationary length process can hide slow convergence.** If `A` consists of
   any `n` orientation fibers, then `π(A)=1/2`, and `μ=π(.|A)` has the stationary
   binomial `K` marginal. Autonomy of the projection makes the entire `K` process
   stationary under this initial law. Domination `μP_t ≤ 2π` bounds the expected
   number of orientation changes by `2tπ(g)`. It follows that
   `||μP_t-π||_TV ≥ 1/2-t 2^(2-n)`, yielding the stated
   `t_mix(full,1/4) ≥ 2^(n-4)`. Convexity correctly transfers this mixed-start
   lower bound to worst-case deterministic-start mixing time.

This reasoning needs neither a canonical formula for `π` nor reversibility.
The general stationary-flow method is standard; see
[Levin–Peres–Wilmer, §7.2 and Chapter 20](https://www.stat.berkeley.edu/~aldous/260-FMIE/Levin-Peres-Wilmer.pdf).
This review does not establish literature priority for the queue application.

## Stronger bound from the orientation cycle

The following improvement is derived in this review. The original bound remains
valid for any half of the orientations; the improvement selects a consecutive half.

The exact orientation moves identify the balanced quotient with `C_(2n)`, with
both directions allowed on each edge. This is only a transition-support fact;
the projected orientation process need not be Markov.

Number its orientations modulo `2n`. For each `j`, let `A_j` be the union of the
`n` consecutive orientation fibers `j,j+1,...,j+n-1`. Conditional uniformity
gives `π(A_j)=1/2` and preserves the stationary binomial length marginal after
conditioning on any `A_j`.

Define the stationary outward flow

```
F(A) = sum_{x in A, y not in A} π(x) Q(x,y).
```

Every directed orientation-changing edge exits exactly one of the `2n` sets
`A_j`: for an edge `i→i+1`, the unique half-arc contains `i` as its last vertex;
for `i→i-1`, it contains `i` as its first vertex. Events preserving orientation
exit none. Summing the stationary flows therefore gives the exact identity

```
sum_j F(A_j) = π(g).
```

Hence some `A=A_j` has `F(A) ≤ π(g)/(2n)`. Start with `μ=π(.|A)`. Its domination
by `2π` bounds the expected number of exits from this particular set by `2tF(A)`.
Being outside `A` at time `t` requires at least one such exit. Thus

```
||μP_t - π||_TV ≥ 1/2 - 2t F(A)
                ≥ 1/2 - t π(g)/n
                ≥ 1/2 - t 2^(1-n)/n.
```

Consequently the stronger lower bound is

```
t_mix(full,1/4) ≥ n 2^(n-3).
```

This improves the supplied lower bound by a factor of `2n`. The stronger
stationary-length initialization statement remains true. The flow averaging
avoids any assumption that individual orientation-edge flows are equal.

## Formalization implications

At the time of this review, the Lean development supplied balanced closure and communication, the
head/full-queue obstruction, exact orientation moves, stationary-vector results,
and the continuous-time path construction. The new mixing theorem still needs
explicit proofs of the Ehrenfest projection and coupling estimate, invariance of
the stationary law under label symmetries, and the total-variation stationary-flow
bound. The improved version also needs the finite half-arc exit-count identity.

At unit rates the total completion rate is the constant `n`, so a clean approach
is to prove the flow bound for the completion kernel and then use its Poisson
time change. No new classification or predecessor enumeration is needed.

This argument is for the balanced family `B_w=T_(2w+1,w)`. The crucial full-queue
obstruction is not supplied for the larger exceptional families with `k>1`, so
the same exponential bottleneck conclusion does not automatically extend to them.
