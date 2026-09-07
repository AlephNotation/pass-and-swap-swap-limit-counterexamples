# Complete-cycle classification: Lean proof status

This development formalizes components of the working proof supplied on
7 September 2026. **The complete operational classification and the new
product-form theorems are not yet formalized.** No theorem assumes the missing
classification as an axiom, and no finite screen replaces a general proof.

The new entry point is `OddCycle/CycleClassification.lean`. It reuses the
repository's original `Valid`, `orientation`, `height`, `carry`, `complete`,
`transition`, and `EventReachable` definitions.

## Checked arbitrary-size results

| Part of the argument | Checked declaration |
|---|---|
| Reachability lifts through communicating fibers | `ReachabilityQuotient.reach_iff` |
| Terminal components correspond under that quotient | `ReachabilityQuotient.terminal_iff` |
| Application to actual queue-state orientation fibers | `CycleState.orientation_reachable_iff`, `CycleState.terminal_orientation_iff` |
| Run count cannot decrease | `CircularRun.Reach.length_le` |
| Deficit cannot increase along a path with unchanged run count | `CircularRun.Reach.deficit_le` |
| Exact terminal classification of the circular-composition rewrite relation | `CircularRun.terminal_iff` |
| Exceptional composition means precisely one long run | `CircularRun.exceptional_iff_one_long` |
| Exceptional composition with an even run count implies `n = 2*k*w + 1` | `CircularRun.exceptional_cycle_length` |
| All parameters `(a,b)` communicate under `(a,b) → (a+w,!b)` at exceptional lengths | `ExceptionalCycle.communication` |
| The parameter space has cardinality `2*n` | `ExceptionalCycle.parameter_count` |
| Alternating-block encoding reconstructs the input word | `CircularWord.encode_linearRuns` |
| Circular extraction yields positive lengths summing to the word length | `CircularWord.circularRuns_positive`, `CircularWord.circularRuns_sum` |
| Nonconstant words yield an even number of circular runs | `CircularWord.circularRuns_even` |
| Actual valid cycle orientations are nonconstant | `orientation_nonconstant` |
| Actual exceptional run patterns require an exceptional cycle length | `exceptionalRuns_cycle_length` |
| No even cycle state has the exceptional run pattern | `even_cycle_not_exceptional` |
| A sufficient path-length budget agrees with the unlimited scan | `carry_eq_unlimited_of_paths` |
| Actual transitions preserve short orientations | `transition_short_orientation` |
| Placement height depends only on orientation | `height_eq_of_orientation_eq` |
| Reachable states of a short state are exactly its orientation fiber | `short_reachable_iff` |
| Every short queue state belongs to a terminal event component | `short_terminal` |
| Terminal components of a finite stochastic kernel have return probability tending to one | `FiniteMarkov.terminal_returnBy_tendsto_one` |
| The corresponding return result for legal completion kernels positive on every event | `CycleState.terminal_returnBy_tendsto_one` |
| Every actual short state has return probability tending to one for those kernels | `CycleState.short_returnBy_tendsto_one` |
| The scan frontier reconstructs the actual limited completion | `scanFrontier_result` |
| The processed part of a scan preserves edge order | `scanFrontier_edgeEquiv` |
| A nonempty untouched suffix certifies budget exhaustion | `scanFrontier_exhausted` |
| Only one cycle neighbor can remain untouched after a positive budget | `scanFrontier_unique_cycle_neighbor` |
| A changed event in either queue can change only the final edge of a directed path of `w+1` edges, with the second-queue placement reversed | `transition_changed_path` |
| Budgets at least `n-1` preserve every valid orientation | `large_budget_preserves_orientation` |

Names in the table are in namespace `OddCycle`. All bounds are arbitrary;
these are structural proofs, not checks up to a selected cycle length.

`CircularRun.Step` acts on lists of run lengths. Its rotation edges reselect
the first run; its other edges are boundary donations and interior splits.
Its terminal theorem is **not** an operational classification theorem until
the correspondence to actual binary orientations and queue events is proved.
Likewise `ExceptionalCycle.Parameter` counts abstract long-run parameters;
the injective correspondence to actual orientations is still required.

## Outstanding obligations

1. Prove the complete local-move lemma in both directions against
   `CycleState.OrientationStep`, including realizability of each permitted
   flip. Necessity is checked as a directed-path statement for both queues;
   its identification with the circular binary-block condition remains.
2. Identify maximal circular runs and their maximum with the original
   directed-path height; connect the binary flip relation to
   `CircularRun.Step`. The extractor's reconstruction, positivity, sum, and
   parity are checked, but these further characterizations are not yet proved.
3. Lift the exceptional parameter moves to the actual orientations, prove
   their injectivity and coverage, and finish Theorem A on actual queue states.
4. Finish eventual entrance and the continuous-time consequences. The
   connection from terminal event components to convergence of finite-step
   return probabilities is checked for legal completion kernels positive on
   every event. A continuous-time sample-path construction, holding times,
   and the associated measure-theoretic transfer are not formalized. The
   `Terminal` predicate itself means a terminal strongly connected component
   of a directed event graph; it does not define recurrence by fiat.
5. Formalize the classwise canonical stationary law for general OI
   prefix-increment allocations, rather than just additive class rates.
6. Prove the new symmetric gained/lost predecessor completeness and its
   general residual `(1 - 2*w*(k-1))/n!` on the actual exceptional class.
   The existing balanced-cycle obstruction remains separate.

These are mathematical proof obligations, not hypotheses hidden in a theorem
named after the requested classification. The supplied Python/JSON checks were
not present in this checkout and are not imported as proof evidence.

## Verify

```sh
lake build OddCycle.CycleClassification
lake env lean OddCycle/CycleClassificationAudit.lean
lake env leanchecker OddCycle.CycleClassification
```

There are no `sorry` declarations, custom mathematical axioms, or native
evaluation axioms in these files.
