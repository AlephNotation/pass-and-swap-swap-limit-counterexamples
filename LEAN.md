# Lean verification

This is a partial formalization of `paper.tex`. It proves balanced-region
nonemptiness, height, closure, and communication with positive position rates
for every w ≥ 2, alongside the five-job certificate results. Lean reconstructs
the replacement dynamics; it does not import the
Python transition tables or assume the Python checks are correct.

## Run

Lean and Mathlib are pinned to 4.28.0. With Elan installed, from this directory:

```sh
lake exe cache get Mathlib.Data.List.Permutation Mathlib.Algebra.Field.Rat Mathlib.Logic.Relation Mathlib.Tactic.NormNum Mathlib.Tactic.Ring Mathlib.Algebra.BigOperators.Ring.List Mathlib.Data.ZMod.Basic Mathlib.Data.List.Sort Mathlib.Data.List.Range Mathlib.Data.List.Sublists
lake build
lake env lean OddCycle/Audit.lean
lake env leanchecker OddCycle
python3 -B code/export_lean_certificate.py --check
```

Allow several minutes for a first build of the finite proofs. Incremental
builds reuse the checked declarations.

`lake build` checks the proofs. The optional `leanchecker` command replays the
project's declarations through Lean's kernel. The final command checks that
the committed Lean data still match the JSON certificate and deterministic
path witnesses; Python is not needed to build or check the Lean proofs.

## What is formalized

The general declarations below are in namespace `OddCycle`:

| Claim | Declaration |
|---|---|
| Every completion preserves the fixed population | `transition_valid` |
| Balanced states exist for every w ≥ 2 | `balanced_nonempty` |
| Exchanging queues preserves balancedness | `balanced_exchange` |
| Every position completion in either queue preserves balancedness, for every w ≥ 2 | `balanced_transition` |
| Every event preserves both validity and balancedness | `balanced_events_closed` |
| Nonemptiness and closure together | `balanced_region_nonempty_closed` |
| Every valid balanced state has height w+1 | `balanced_height` |
| States with the same orientation communicate | `reachable_of_orientation_eq` |
| All valid balanced states communicate through queue-position completions | `balanced_communication` |
| Every path from the balanced region stays in it | `balanced_reachable_closed` |
| Communication with an explicit positive-rate hypothesis (Lemma 4) | `balanced_positive_rate_communication` |

These prove the nonemptiness and closure assertions of Lemma 2. Its general
cardinality formula is not yet formalized. Closure uses the original
`Model.lean` definitions and has no rate assumptions: assigning arbitrary
nonnegative rates, including zero, selects from events already proved safe.

The height and communication theorems also quantify over every w ≥ 2.
`EventStep` uses the original `transition` function and is proved equivalent
to membership in `events`. `PositiveEventStep` additionally requires the
initiating position's rate to be positive. The rate hypothesis is required
only at occupied positions in valid balanced states; rates may depend on the
entire configuration and may be real-valued. These are finite-path theorems,
without any assumed Markov-chain recurrence or uniqueness result.

The five-job results are:

| Claim | Declaration in `OddCycle.FiveJob` |
|---|---|
| Support is exactly all valid balanced C5 states | `mem_support_iff` |
| 180 states, without repetitions | `support_size`, `support_nodup` |
| Every state has height three | `support_height` |
| Closure under every position completion with budget two | `support_closed` |
| Communication using only head completions | `head_communication` |
| Explicit proper three-coloring of C5 | `proper_three_coloring` |
| Canonical balance defect is exactly −1/360 | `canonical_defect` |
| Any nonzero rational rescaling of canonical weights fails stationarity | `canonical_scaled_not_stationary` |
| Positive integer certificate, exact total, every balance equation | `certificate_positive`, `certificate_total`, `certificate_stationary` |
| Normalized rational weights are positive, sum to one, and are stationary | `probability_positive`, `probability_sum`, `probability_stationary` |
| Certificate cannot factor as K A(c) B(d), even after normalization | `normalized_certificate_not_product` |

The factorization theorem quantifies over every characteristic-zero field,
including real-valued factors. The balance equations and probability vector
are currently expressed over the rationals, at rates (2,1,1,1,1).

## Definitions and trust

- `OddCycle/Model.lean` defines the general finite-cycle transition rule,
  fixed-population states, orientations, balanced orientations, directed-path
  height, canonical prefix weights, and row-generator balance. It also proves
  that the state enumeration includes exactly all fixed-population states.
- `OddCycle/Certificate.lean` contains integer weights and finite head paths.
  They are untrusted candidate data exported by
  `code/export_lean_certificate.py` from the bundled certificate and Python
  model. Lean independently checks their support, paths, and balance.
- `OddCycle/FiveJob.lean` checks the finite claims and proves the rectangle
  obstruction. `OddCycle/Balance.lean` proves the general scaling identity;
  `OddCycle/Conclusions.lean` handles normalization.
- `OddCycle/Operational.lean` proves population preservation.
  `OddCycle/EdgeOrder.lean` proves a general replacement invariant using
  two-letter projections of queue words. `OddCycle/PlacementOrder.lean`
  connects these projections to the model's orientation definition.
- `OddCycle/CycleCoordinates.lean`, `OddCycle/CycleGeometry.lean`, and
  `OddCycle/CycleSymmetry.lean` establish the cyclic coordinate identities.
  `OddCycle/BalancedGeometry.lean` and `OddCycle/BalancedSymmetry.lean`
  connect them to balanced states. `OddCycle/GeneralClosure.lean` proves
  closure for arbitrary w ≥ 2.
- `OddCycle/GeneralHeight.lean` bounds every directed path by the existing
  rank function and exhibits a long-branch path attaining height w+1.
- `OddCycle/Reachability.lean` constructs tail and adjacent-exchange paths.
  `OddCycle/WordCommunication.lean` proves communication within a fixed
  orientation. `OddCycle/BalancedMoves.lean` verifies explicit head completions,
  and `OddCycle/GeneralCommunication.lean` connects all balanced orientations
  and proves communication under positive position rates.
- `OddCycle/Audit.lean` prints the axioms used by the main declarations.

Finite calculations use `decide +kernel`. There are no admitted proofs,
custom mathematical axioms, or native-evaluation axioms in the project.
The audit reports only the standard axioms `propext`, `Classical.choice`,
and `Quot.sound`; some declarations require none.

The integer certificate is not a definition of the state space: its support
is proved equivalent to validity and balanced orientation, with an exhaustive
check against all 720 configurations. Stationarity sums events, retaining
their multiplicity and the initiating job's rate. The canonical defect is
computed directly from the transition rule, without assuming the manuscript's
predecessor table or the unlimited product-form theorem.

## General closure proof

The proof is structural, with no enumeration of cycle sizes. In a balanced
orientation, assign each vertex its distance from the source along its
branch, assigning the common sink rank w+1. Every replacement increases
rank. Once a budget of w replacements is exhausted, any further compatible
vertex must form the edge from the long branch's penultimate vertex to the
sink. The generic queue invariant proves that all other edge orders are
preserved.

Reversing that one edge produces the other balanced orientation with the
same source. Thus either possible order of its endpoints gives a balanced
successor. Exchanging queues reverses the placement word and reduces the
second-queue case to the first. This argument proves the operational claim
directly, without assuming unlimited orientation preservation.

## General height and communication proofs

The rank invariant bounds the number of edges in every directed path by
w+1. The long branch occurs as a subsequence of every placement with the
given balanced orientation and attains this bound. This proves equality
for the original `height` definition, which enumerates adjacency chains
among placement subsequences.

For communication, tail completions move the cut without changing the
placement word. An adjacent incompatible pair can be exchanged by putting
the cut just after it and completing its first job. An induction moves each
desired label to the front, proving that placements with the same edge
orders communicate. An explicit head completion on a canonical branch word
flips the long-branch direction. Conjugating this move by queue exchange,
then toggling again, advances the source one vertex. Repetition connects
every source and both directions. Finally, closure ensures that every
completion used in these paths receives a positive rate under the stated
rate hypothesis.

## Remaining work

The manuscript as a whole is **not yet verified in Lean**. In particular:

1. The all-w cardinality formula in Lemma 2.
2. The uniform two-flow completeness lemma and the all-parameter balance
   formula, including the imported unlimited product-form theorem.
3. General finite continuous-time Markov-chain results connecting a closed
   communicating event graph to recurrence and uniqueness of its stationary
   distribution. The finite graph and stationary-vector ingredients are
   checked here; these probabilistic conclusions are not yet formal theorems.
4. The C7 classification, small-graph screen, and other finite experiments.
