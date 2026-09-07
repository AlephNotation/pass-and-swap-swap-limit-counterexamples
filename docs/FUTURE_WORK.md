# Preserved mixing work: completed lemmas and open obligations

This material is separate from the classification manuscript's claims.
All existing Lean code remains in the default build and axiom/kernel audits.
No exponential queue-mixing theorem is claimed and no attempt to finish it
is part of this editorial revision.

## Completed declarations

All names have prefix `OddCycle.`.

| Declaration | Proved scope |
|---|---|
| `balanced_orientation_change_head`, `balanced_orientation_change_boundary`, `balanced_orientation_change_unique_position` | Actual orientation-changing events in the first exceptional family `B_w`, w>=2: a full-queue head is necessary. This is not established for larger exceptional cycles. |
| `FiniteMarkov.evolve_simplex`, `FiniteMarkov.evolve_dominated` | Iterates of a finite stochastic kernel; preservation of probability vectors and a pointwise domination bound. |
| `FiniteMarkov.bottleneck_lower`, `FiniteMarkov.half_bottleneck_lower` | Finite discrete kernel, supplied stationary vector and bottleneck set: lower bounds from stationary exit flow. |
| `FiniteMarkov.poisson_first_moment`, `FiniteMarkov.poissonEvolve_simplex`, `FiniteMarkov.poissonEvolve_stationary` | The explicitly defined Poisson average of kernel iterates. |
| `FiniteMarkov.poisson_bottleneck_lower`, `FiniteMarkov.poisson_half_bottleneck_lower` | Bounds for that Poisson average, under their stationary-flow hypotheses. |

Source modules: `BalancedBottleneck.lean`, `FiniteEvolution.lean`,
`FiniteBottleneck.lean`, `PoissonEvolution.lean`, and their dependencies.
`StructuralTheoryAudit.lean` audits these results. The completed queue-length
path-law consequence has a different proof and does not discharge the
quantitative obligations below.

## Outstanding obligations for a queue-specific mixing theorem

Fix a single family and allocation throughout, such as `B_w` with unit
position rates. A quantitative proof would still need to establish the
required stationary symmetry and conditional orientation distribution,
count the stationary flow across a specified orientation cut, and bound
the relevant configuration masses and actual transition rates. It must
identify the Poisson-averaged evolution with the constructed clocked queue
law before transferring its bound to physical time. A claimed separation
from queue-length mixing would additionally need the length-coupling bound.

The full-queue obstruction must not be transferred from `B_w` to
`T_(2kw+1,w)` with k>=2 without proof. Equality of queue-length observation
laws establishes no timescale and no lower bound on the size of a transient
full-state discrepancy.
