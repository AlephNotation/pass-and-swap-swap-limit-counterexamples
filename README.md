# Odd-cycle traps and product-form failure: complete package

[![DOI](https://zenodo.org/badge/1359616826.svg)](https://doi.org/10.5281/zenodo.22575717)

Start with **paper.pdf**, the consolidated manuscript. **paper.tex** is its
self-contained LaTeX source. This package merges the uniform theorem with the
earlier five-job nonfactorization certificate and finite graph experiments.

A **Lean 4 formalization** proves the general balanced-region cardinality,
height, closure, communication, two-flow identity, and canonical defect for
every w >= 2, alongside the five-job certificates. It also proves finite-chain
return-probability and stationary-law results and connects them to the queue
model. The cycle extension constructs the continuous-time process and proves
its recurrence and absorption results. Finite experiments remain separate.
See [LEAN.md](LEAN.md) for the exact proof scope and build commands.

The new [cycle-classification formalization](OddCycle/CycleClassification.lean) proves
the arbitrary-size recurrent-class classification, general positive OI laws on
short classes, and the sharp canonical boundary `n % (2*w) != 1`. It includes
the larger-cycle unit-rate counterexamples and the explicit C9/w=2 residual.
The continuous-time process is measurable and nonexplosive; an executable
recurrence classifier has a proved linear bound in a word-RAM cost model.
This extension is separate from the consolidated manuscript above.

The [structural extension](OddCycle/StructuralTheory.lean) proves that queue-length
generators under position-indexed service are independent of the swapping
graph and budget. It also proves canonical length marginals and an arbitrary-size
family where all length-observable balance identities hold despite full
canonical failure. The document develops a stronger slow-mixing argument;
that continuous-time mixing theorem is not yet fully formalized.

The [queue-length indistinguishability theorem](OddCycle/QueueLengthIndistinguishability.lean)
is now formalized for every unit-rate `C_(2kw+1)`, `w >= 1`, `k >= 2`.
The nonstationary normalized canonical candidate and an actual stationary
initialization give exactly the same law of the entire continuous-time
queue-length trajectory. The theorem includes cancellation of the residual at
every length and an explicit C9/w=2 example in the same model.
The exact assumptions, residual, and verification commands are recorded in
[LEAN.md](LEAN.md#exact-queue-length-indistinguishability).

## One-command verification

Python **3.10 or newer**, standard library only:

```sh
python3 run_checks.py
```

The suite reconstructs the model, verifies every requested check, and compares
fresh deterministic JSON with all recorded results. It exits nonzero on a failed
identity or a mismatch. It does not use the network or modify its data files.
On Windows, `py -3` may replace `python3`.

All checks remain active under optimization:

```sh
python3 -O run_checks.py
```

The full suite enumerates more than a million transitions; allow time for it to
finish. To save fresh result copies, use `--output-dir PATH`. No command uses
floating-point tolerances or stochastic simulation.

## What the results establish

| Result | Scope | Basis |
|---|---|---|
| Balanced-region closure and recurrent-state existence | Every w >= 2; every admissible OI allocation | Written proof |
| A single recurrent class B_w | Every w >= 2; positive service at every position | Written proof |
| Canonical prefix-product failure | Every w >= 2; one class rate theta > 0 with theta != 1, all others rate 1 in both queues | Written two-flow calculation |
| No alternative factorization K*A(c)*B(d) | w=2, theta=2 | Exact positive integer stationary certificate and a nonzero rectangle determinant |
| Head-only connectivity of B_2 | All admissible OI allocations | Written nine-orbit argument; exhaustive finite verification |
| B_w is exactly the tall recurrent set | C5/w=2 and C7/w=3; head-only and all-position event graphs | Complete-state SCC classification |
| No tall recurrent states in the small-graph screen | 61 non-isomorphic simple bipartite graphs on 1..6 vertices at w=1; four named w=2 graphs | Complete-state reachability checks |

The classification does **not** assert that every height-(w+1) state is balanced.
For C7 at w=3 there are 3,248 height-four states; only 1,120 are recurrent.
The two-flow theorem concerns the canonical product. The arbitrary-factor
exclusion is not claimed for every w. The one-swap general case remains open
in this work.

## Direct component commands

```sh
python3 code/verify_five.py --certificate data/stationary_certificate.json
python3 code/verify_orbits.py
python3 code/verify_uniform.py
python3 code/verify_classification.py
python3 code/verify_screen.py
```

`verify_uniform.py` defaults to all balanced states at w=2,3,4,5 with four
rational rate choices, complete-space changed-predecessor audits at w=2,3,
and explicit-word tests through w=50. Finite tests supplement the all-w proof.

`verify_screen.py` independently regenerates all bipartite isomorphism classes
through six vertices by vertex addition and degree-partitioned canonical
labeling. The bundled graph list is then checked for exact coverage before the
queue experiments run; no NetworkX installation is required.

## Regenerate the stronger stationary certificate

Checking the certificate requires no stationary solver. To reproduce its
construction as well, run:

```sh
python3 code/regenerate_certificate.py --output regenerated_certificate.json
python3 code/verify_five.py --certificate regenerated_certificate.json
```

The generator uses rational Gaussian elimination on the remaining 45 symmetry
orbits, then supplies weights on all 180 states. The verifier reconstructs the
full generator and checks all balance equations directly. It rejects a changed
weight, missing state, or invalid support.

## Build the paper

No bibliography or image files are needed. A standard LaTeX installation with
the packages named in the preamble is sufficient:

```sh
pdflatex paper.tex
pdflatex paper.tex
```

## Citation

If you use the results, code, or Lean proofs, please cite:

```bibtex
@misc{daly2026oddcycle,
  author = {Daly, Tynan},
  title  = {{Odd-Cycle Traps and Product-Form Failure in Limited Pass-and-Swap Queues}},
  year   = {2026},
  doi    = {10.5281/zenodo.22575717},
  url    = {https://doi.org/10.5281/zenodo.22575717}
}
```
