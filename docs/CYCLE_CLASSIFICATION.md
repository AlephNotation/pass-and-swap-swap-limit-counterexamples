# Cycle classification: Lean formalization

The arbitrary-size operational classification, positive OI product form, and
sharp canonical boundary are now the main results of `paper.tex` and are proved
in Lean. The authoritative statement-and-assumption map is [LEAN.md](../LEAN.md). The new
unit-rate residual is proved on the actual exceptional recurrent class for
all `w ≥ 1, k ≥ 2`, including completeness of both predecessor lists.
The continuous-time recurrence and absorption statements and the linear-time
classifier claim are also formalized, with the cost model specified below.

Entry point: `OddCycle/CycleClassification.lean`. The development uses the
original repository definitions of `Valid`, `orientation`, `height`, `carry`,
`complete`, `transition`, and `EventReachable`. It does not replace the queue
model with an assumed run rewrite rule or assume the paper's product-form theorem.

## Main statements

All declarations below are in namespace `OddCycle`.

| Result | Declaration |
|---|---|
| Exact operational orientation moves | `orientationStep_iff_circularFlip` |
| Recurrence test on actual queue states | `CycleState.terminal_iff_runs` |
| All closed communicating classes are short fibers or the unique exceptional family | `closed_class_classification` |
| Short class equals its entire orientation fiber | `short_reachable_iff`, `ClosedClass.short_fiber` |
| Tall class exists exactly at `n = 2*k*w + 1` | `exists_tall_terminal_iff` |
| Every position completion preserves the exceptional set, independently of rates | `exceptionalRuns_transition` |
| All exceptional queue configurations communicate | `exceptionalRuns_communicate` |
| Exceptional class has exactly `2*n` actual orientations | `exceptional_orientation_count` |
| Previous balanced class is the `k=1` exceptional class, for `w ≥ 2` | `balanced_is_exceptional` |
| Completion probabilities constructed from arbitrary positive position rates | `PositivePositionAllocation.kernel`, `kernel_pos_iff` |
| Return probability tends to one exactly at the classified states | `PositivePositionAllocation.recurrent_iff_runs` |
| Probability of avoiding all recurrent states tends to zero | `PositivePositionAllocation.classified_absorption` |
| At nonexceptional lengths, probability of avoiding all short states tends to zero | `PositivePositionAllocation.short_absorption` |
| Under nonnegative event support, the exceptional set still contains a recurrent state | `CycleState.exceptional_recurrent_state` |
| General unlimited OI predecessor identity | `OICapacity.unlimited_partial_balance` |
| General unlimited OI canonical balance | `unlimited_oi_stationary` |
| Normalized positive canonical law on each short class | `short_class_normalized_oi` |
| Normalized canonical law on every recurrent class at safe lengths | `ClosedClass.safe_normalized_oi` |
| Every even cycle is safe | `even_recurrent_oi_stationary` |
| Complete gained and lost event lists for the unit-rate family | `unit_gained_predecessors`, `unit_lost_predecessors` |
| Actual target orientation and exceptional gained-source membership | `unit_target_orientation`, `unit_gain_exceptional` |
| Exact residual `(1 - 2*w*(k-1))/n!` for every larger exceptional cycle | `unit_exceptional_residual` |
| Unit allocation fails canonical stationarity there | `unit_exceptional_not_stationary` |
| Universal canonical stationarity iff `n % (2*w) ≠ 1`, for `w ≥ 2` | `cycle_canonical_sharpness` |
| The same equivalence for normalized probability weights | `cycle_normalized_canonical_sharpness` |
| Explicit C9 / w=2 residual `-1/120960` | `NineJobCycle.residual` |
| Measurable continuous-time queue process | `PositivePositionAllocation.process_measurable` |
| Completion epochs diverge: no explosion | `PositivePositionAllocation.process_nonexplosive` |
| Exponential completion law and exact service-rate identity | `PositivePositionAllocation.completion_law`, `completion_rate_identity` |
| Actual continuous-time recurrence iff the run criterion | `PositivePositionAllocation.continuous_recurrent_iff_runs` |
| Almost-sure absorption, and short absorption at safe lengths | `PositivePositionAllocation.continuous_classified_absorption`, `continuous_short_absorption` |
| Almost every timed path eventually stays in one classified communicating class | `PositivePositionAllocation.continuous_eventually_one_class` |
| Executable rank-array classifier with a linear cost bound | `CycleClassifier.classify_continuous_recurrence` |

`ClosedClass` means a nonempty, duplicate-free list of valid queue states,
closed under every actual completion, with every pair connected by actual
completion events. Class comparisons use list permutation, so enumeration
order has no mathematical significance. The recurrence and classification
predicates are defined independently; their equivalence is proved.

## Product-form proof and sharpness

`OICapacity` is a permutation-invariant total service capacity with zero empty
capacity. Its occupied-position rates are the actual prefix increments.
`PositiveOIAllocation` requires strictly positive increments on every valid
queue prefix. Both queues may have different allocations.

The unlimited balance proof reverses all incoming scans and telescopes their
weights. The predecessor parametrization is proved complete. On short classes,
limited and unlimited events coincide, giving canonical balance; positivity
then supplies a finite, positive normalizer and a probability distribution.
`oiBalance_eq_positionGenerator` identifies this balance expression with the
sum over the original queue-position events, including diagonal subtraction.

For sharpness, `unit_exceptional_residual` constructs the interior topological
order, verifies both target and gained source are in the exceptional class,
and counts exactly one gained event and `2*w*(k-1)` lost events. The helper
lemmas' support-membership premises are discharged in this theorem. For `k=1`,
`oiBalance_additive` connects the general OI generator to the existing
rate-two defect proof. The final equivalence quantifies over all positive OI
allocations and all actual closed communicating classes.

The concrete C9 instance is:

- Swapping graph: edges `{i,(i+1) mod 9}`.
- Budget: `w=2` replacements; the initiating completion is not counted.
- Allocation: rate one at every occupied position in both queues.
- Target, head to tail: `([0], [7,8,6,3,4,5,2,1])`.
- Gained source: `([], [7,8,0,6,3,4,5,2,1])`, completing the second-queue head.
- Canonical weight: `1/(|c|! |d|!)`.
- Balance residual at the target: `-1/120960`.

`NineJobCycle.target_member`, `recurrent_class`, `gained_event`, and `residual`
check these claims; the residual specializes the general proof rather than
enumerating all C9 states.

## Probability conventions and scope

The completion kernel is constructed from arbitrary positive, state-dependent,
time-homogeneous position rates; OI allocations instantiate it directly.
`MarkovPathMeasure` constructs an infinite trajectory measure by Ionescu--Tulcea.
`MarkovPathHitting` and `MarkovPathReturn` identify finite avoidance and return
formulas with measurable events on that space. No lumpability is assumed.

`ExponentialClocks` constructs independent unit exponential clocks and proves
that they are positive and have divergent sum almost surely, using
Borel--Cantelli. Restricting to this measure-one set gives a probability space
on which every clock path has these properties. `ClockedPath` divides each
clock by the current state's total rate. Finite state space and positive rates
give strictly increasing, divergent completion epochs. `TimedStateMeasurable`
checks the state at each real time is measurable and constant between epochs.

The trajectory and clocks have a product law. `TimedJumpLaw` proves the first
completion's exponential waiting law and destination probabilities. The total
rate times each destination probability equals the sum of the corresponding
original position rates. Almost every trajectory uses legal transitions.
`CycleContinuousTime` proves recurrence on this timed probability space and
almost-sure eventual residence in one classified communicating class. Return
means visiting the starting state after the first completion epoch, excluding
the initial holding interval. The stationary statements use the original
continuous-time generator's balance equations.

## Executable classifier and complexity

`CycleClassifier.classify n w s` returns a Boolean and its instrumented cost.
It builds `c ++ reverse(d)`, writes each label's rank to an array, reads the
cycle's edge bits, extracts circular runs, and scans the run lengths once.
`classify_correct` identifies its answer with the original `ShortRuns` or
`ExceptionalRuns` predicates. `classify_continuous_recurrence` proves that the
answer is true exactly when the continuous-time return event has probability
one, and that its cost is at most **`33*n + 18`** for every valid input.

The cost model counts bounded word-RAM operations: list inspection and cons,
array read/write, word arithmetic, and comparisons. It explicitly charges all
list traversals and array initialization. Array construction uses a single
mutable owner; array updates are constant-cost RAM operations. Words must hold
the input budget and intermediate integer quantities. The claim is O(n) in
this model, not arbitrary-precision bit complexity, Lean kernel reduction
time, or a guarantee about a particular compiled executable's wall time.

## External claims and experiments

Literature priority and the reported exhaustive Python/JSON experiments are
not Lean proofs. `cycle_checks.json`, `symmetric_checks.json`, and `nine_job_checks.json` were
not present in this checkout. Their historical claims are not imported as
verification records. The complete C9 check is now reproduced by
`code/verify_nine.py` in `results/nine_job.json`, including the 131,040-state
count, 1,179,360 events per generator, and the integer residual -3. Existing
finite classifications and graph screens retain their separate Python checks.

These distinctions do not supply assumptions to the classification, OI balance,
or sharpness theorems. No theorem assumes its intended conclusion. No external
mathematical peer review is claimed.

## Verification

```sh
lake build
lake env lean OddCycle/CycleClassificationAudit.lean
lake env leanchecker OddCycle.CycleClassification
```

The audit lists dependencies of the principal declarations. They use only
Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms (or fewer).
There are no admitted proofs, custom mathematical axioms, or native-evaluation
axioms. The main results have arbitrary bounds; finite calculations are confined
to concrete specializations and use kernel-checked reduction.

The sharp equivalence requires `w >= 2`; recurrence and safe-length sufficiency
require only `w >= 1`. See the quantifier review in LEAN.md. This revision
is consolidated into the manuscript, rather than an unmerged mathematical extension.
