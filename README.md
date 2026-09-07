# Recurrence and Product-Form Stationarity in Swap-Limited Queues on Cycles

[Paper (PDF)](paper.pdf) · [Editable LaTeX](paper.tex) · [Theorem/Lean map](LEAN.md) · [Verification package](PACKAGE.md)

The manuscript classifies all recurrent configurations of two closed-tandem
queues with one distinct job per vertex of `C_n`, `n >= 3`, and replacement
budget `w >= 1`, under strictly positive service at every occupied position.
Each short orientation (all circular run lengths at most `w`) gives one closed
communicating class. The only other class is `T_(n,w)`: exactly one run has
length `w+1`, and all others have length `w`. It exists exactly at
`n=2kw+1`, `k >= 1`, is unique, and contains exactly `2n` orientations with
all their linear extensions and cuts. All other configurations are transient.

For `n >= 3`, **`w >= 2`**, canonical product form is stationary on every
closed class **for every pair of strictly positive OI allocations** if and
only if `n % (2*w) != 1`. This is a universal statement over allocations:
an exceptional length has a failing allocation, not necessarily failure for
every allocation. Safe-length sufficiency holds already for `w >= 1`.
Every even cycle is safe under these hypotheses.

The classification and sharp boundary are now the manuscript's main results.
Lean proves them for arbitrary parameters from the actual queue transitions;
the numerical enumerations below have separately stated finite scopes.
See [classification details](docs/CYCLE_CLASSIFICATION.md) and
[the checked revision and commands](verification/REPORT.md).

## Results and their scopes

| Result | Assumptions / support | Evidence |
|---|---|---|
| Complete recurrent-class classification, exceptional uniqueness and `2n` orientations | `n >= 3`, `w >= 1`; positive service at every occupied position | Structural proof and Lean |
| Exceptional closure; existence of a recurrent state | `n=2kw+1`, `w,k >= 1`; closure survives nonnegative event rates | Structural proof and Lean |
| Sharp universal canonical boundary | `n >= 3`, `w >= 2`; both queues have positive OI prefix increments | Structural proof and Lean |
| First exceptional case `B_w=T_(2w+1,w)`; exact two-flow formula | `w >= 2`; identical additive allocations `r_0=theta>0`, other rates one; nonzero for `theta != 1` | Written calculation and Lean |
| Larger exceptional-family canonical failure | `w >= 1`, `k >= 2`; unit rate at every position; residual `[1-2w(k-1)]/n!` | Written calculation and Lean |
| C9/w=2 target `([0],[7,8,6,3,4,5,2,1])` | Unit position rates; unnormalized residual `-1/120960` | Lean specialization and complete class enumeration |
| No factorization `K*A(c)*B(d)` | C5/w=2, rates `(2,1,1,1,1)` in both queues | Exact stationary certificate, nonzero rectangle determinant, Lean |
| Head-only communication of `B_2` | Every admissible OI allocation, even with zero non-head rates | Nine-orbit proof, Lean connectivity, finite checks |
| C5/w=2 and C7/w=3 state counts and head-only classifications | Entire finite state spaces; both event supports | Python SCC checks; all-position structure also follows from general Lean theorem |
| One-swap bipartite screen | All 61 nonisomorphic simple bipartite graphs through six vertices | Python exact graph coverage and reachability checks |

The odd-cycle examples at `w=1` do not satisfy Conjecture 1's bipartite
hypothesis. The arbitrary-graph one-swap bipartite problem remains unresolved.
The five-job exclusion of *all* queue-wise factors is not generalized to all
exceptional cycles. On the family `n=2w+1`, canonical balance at `theta=1`
for the tested `w=2,3,4,5` is computational evidence, not an all-`w` theorem.

At unit position rates, queue length decreases at rate `K` and increases at
rate `n-K`, regardless of order, graph, or budget. Equal numbers of cuts at
each length make the canonical marginal correct on a closed class. On the
proved larger exceptional family, the nonstationary canonical candidate and
a stationary law therefore give the same entire length-process law. This
short consequence is in the paper; [path-law details](LEAN.md#exact-queue-length-indistinguishability)
remain in the formalization. It does not establish a mixing timescale.
The preserved, unfinished mixing work is scoped in [future work](docs/FUTURE_WORK.md).

## Verification

Python 3.10 or newer, standard library only:

```sh
python3 run_checks.py
python3 -O run_checks.py
```

The suite reconstructs transitions, checks exact certificates and graph
coverage, and compares fresh output with every `results/*.json` file. It
does not use simulation, tolerances, or the network. `--output-dir PATH`
saves fresh copies. The C9 check enumerates all 131,040 exceptional states
and 1,179,360 events per generator, comparing two transition implementations.

```sh
lake build
lake env lean OddCycle/Audit.lean
lake env lean OddCycle/CycleClassificationAudit.lean
lake env lean OddCycle/StructuralTheoryAudit.lean
lake env lean OddCycle/IndistinguishabilityAudit.lean
lake env leanchecker --verbose OddCycle
python3 -B code/export_lean_certificate.py --check
```

All Lean modules, including the preserved structural and path-law proofs,
remain in the default build. [PACKAGE.md](PACKAGE.md) gives the complete
verification runner, toolchain setup, certificate regeneration, PDF build,
file hashes, and archive instructions. [LEAN.md](LEAN.md) records precise
declarations and logical dependencies.

## Regenerate the stationary certificate

```sh
python3 code/regenerate_certificate.py --output /tmp/regenerated_certificate.json
python3 code/verify_five.py --certificate /tmp/regenerated_certificate.json
```

Rational Gaussian elimination constructs weights using 45 symmetry orbits;
the independent verifier checks all 180 original states and every balance
equation. The exact certificates, graph inputs, and expected outputs remain
editable and included.

## Build the manuscript

`paper.tex` is self-contained, with an inline bibliography and no external
figures or private source dependencies. With standard LaTeX packages:

```sh
pdflatex paper.tex
pdflatex paper.tex
```

Alternatively, `tectonic paper.tex` performs the necessary reference passes.
The recorded verification uses two complete Tectonic builds and inspects the
rendered pages. See [citation audit](docs/CITATION_AUDIT.md) for publisher-PDF
page locations. [email.txt](email.txt) is an unsent covering draft.

## Citation and archive status

The existing public archive [10.5281/zenodo.22575717](https://doi.org/10.5281/zenodo.22575717)
is the earlier release; this local manuscript consolidation does not update
that archive. Cite this revision by its title and the commit recorded in the
verification report. `CITATION.cff` describes this repository revision and
identifies the earlier archive separately.
