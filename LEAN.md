# Lean verification

Lean checks the general balanced-region, two-flow, and canonical obstruction
arguments for every w ≥ 2, as well as the five-job certificate. It also proves
the finite Markov-chain recurrence and stationary-vector results and connects
them to the queue's original transitions and balance equations.

The cycle extension also constructs the continuous-time sample-path process
from the completion kernel and independent exponential clocks. Lean checks
measurability, nonexplosion, recurrence, and almost-sure absorption into one
communicating class. The C7 classification, graph screen, and other finite
experiments retain their separate Python checks.

Lean reconstructs the replacement dynamics. It does not import Python
transition tables or assume the Python checks are correct.

The [structural-theory extension](STRUCTURAL_THEORY.md), imported by the default
build, proves the queue-length generator and canonical-marginal identities,
including full canonical defects invisible to length-observable balance tests.
It also supplies generic finite-kernel and Poisson-averaged bottleneck bounds.
The complete continuous-time queue mixing theorem still has the explicitly
listed obligations in that document. Its audit is
`OddCycle/StructuralTheoryAudit.lean`.

The [exact indistinguishability theorem](QUEUE_LENGTH_INDISTINGUISHABILITY.md)
connects the unit-rate exceptional family's canonical failure to equality of
entire continuous-time length-trajectory laws. Its comparison initialization
is proved invariant at every physical time, using the existing exponential
clock construction. The audit is `OddCycle/IndistinguishabilityAudit.lean`.

## Run

Lean and Mathlib are pinned to 4.28.0. With Elan installed, run from this
directory:

```sh
lake exe cache get
lake build
lake env lean OddCycle/Audit.lean
lake env leanchecker --verbose OddCycle
python3 -B code/export_lean_certificate.py --check
```

The cache command downloads prebuilt Mathlib dependencies. Allow several
minutes for a first build of the finite proofs. Incremental builds reuse the
checked declarations.

`lake build` checks the proofs. `Audit.lean` prints the axioms used by the
principal claims. `leanchecker` independently replays the project's compiled
declarations through Lean's kernel. The Python command checks
that the committed certificate data still match their JSON source and
deterministic path witnesses; Python is not needed to check the Lean proofs.

## General queue theorems

These declarations are in namespace `OddCycle`:

| Claim | Declaration |
|---|---|
| Every completion preserves the fixed population | `transition_valid` |
| Balanced states exist for every w ≥ 2 | `balanced_nonempty` |
| Every queue-position completion preserves balancedness | `balanced_transition`, `balanced_events_closed` |
| Nonemptiness and closure together | `balanced_region_nonempty_closed` |
| Exact cardinality: 2(2w+1)(2w+2) choose(2w−1,w) | `balanced_cardinality` |
| Every valid balanced state has height w+1 | `balanced_height` |
| States with the same orientation communicate | `reachable_of_orientation_eq` |
| All valid balanced states communicate | `balanced_communication` |
| Every intermediate state stays balanced and valid | `balanced_reachable_closed` |
| Lemma 4 with positive position rates explicit | `balanced_positive_rate_communication` |
| Proper coloring using exactly w+1 nonempty colors | `partiteColor_proper`, `partiteColor_surjective` |
| Only full-queue head events can change with the budget | `balanced_changed_event_head` |
| Unique source reconstruction for a changed incoming event | `balanced_changed_head_injective` |
| Exactly the gained X and lost Y events in Lemma 5 | `two_flow_completeness` |
| Difference of limited and unlimited balance, with arbitrary weights and class rates | `two_flow_balance_difference` |
| Exhaustive unlimited incoming-event list at the target | `targetOccurrences_complete` |
| Unlimited canonical balance at the target, proved directly | `unlimited_target_balance` |
| Uniform two-flow identity W(X)−W(Y) | `uniform_two_flow_identity` |
| Displayed balance formula for every positive real theta | `uniform_defect` |
| Positive defect below theta=1, negative above it | `uniform_defect_pos`, `uniform_defect_neg` |
| Defect −w/(2w+2)! over any characteristic-zero field | `uniform_defect_two` |
| Every nonzero real rescaling fails stationarity when theta≠1 | `uniform_scaled_not_stationary` |
| Normalized canonical weights are positive and sum to one | `normalizedCanonicalWeight_pos`, `normalizedCanonicalWeight_sum` |
| These normalized weights fail stationarity when theta≠1 | `normalizedCanonicalWeight_not_stationary` |

All assertions of Lemma 2 are proved. Closure has no rate assumptions:
arbitrary nonnegative rates, including zero, select from events already
proved safe. Communication allows rates to depend on the entire state,
queue, and position, and requires positivity only at occupied positions.

The balance definitions are polymorphic over fields. The two-flow difference
holds for arbitrary weights and class rates. The field version of the
canonical formula states its nonzero-denominator hypotheses explicitly;
the real version derives them from theta>0. No unlimited product-form
stationarity theorem is assumed.

## Finite probability and stationary laws

`FiniteMarkov S` consists of a finite matrix of nonnegative real transition
probabilities whose rows sum to one. It is not a reachability predicate.

`avoid target n i` computes the probability of avoiding the target at times
0 through n, starting at i, by the finite first-step recursion. Consequently,
`returnBy target n = 1 - expect (avoid target n) target` is the probability of
a positive-time return by step n+1. The proofs establish convergence of
these probabilities to one, rather than defining recurrence as membership
in a terminal graph component.

| Claim | Declaration |
|---|---|
| Finite communication implies return probabilities tend to one | `FiniteMarkov.returnBy_tendsto_one` |
| Every nonempty finite chain has a stationary probability vector | `FiniteMarkov.stationary_exists` |
| A communicating chain has a unique, strictly positive stationary probability vector | `FiniteMarkov.stationary_exists_unique`, `FiniteMarkov.stationary_positive` |
| Every nonempty finite closed set contains a recurrent state in the original chain | `FiniteMarkov.closed_recurrent_state_exists` |
| Any finite completion kernel on the full population has a balanced recurrent state of height w+1 | `balanced_recurrent_state` |
| The queue's embedded matrix is irreducible for theta>0 | `queueMarkov_irreducible` |
| Every balanced state has return probability tending to one | `queue_returnBy_tendsto_one` |
| Embedded-matrix stationarity equals the original generator balance equations | `queue_stationary_iff` |
| Existence and uniqueness for those original balance equations | `queue_stationary_exists_unique` |
| The unique stationary probabilities are strictly positive | `queue_stationary_positive` |
| The normalized canonical vector is not stationary for theta≠1 | `queue_normalized_not_stationary` |

`balanced_recurrent_state` quantifies over any stochastic matrix on the
original full population whose positive-probability transitions are legal
completions or self steps. No irreducibility or positive non-head-rate
hypothesis is imposed. Closed-set restriction is proved to preserve the
original return probabilities.

For the paper's distinguished-rate allocation, `queueMarkov` is constructed
explicitly from `events`, keeping event multiplicity and the initiating
job's rate. Its total event rate is proved to be theta+2w. Dividing incoming
rates by this constant gives the embedded matrix; `queue_stationary_iff`
proves its equivalence to the original row-generator equations.

The return proof takes the decreasing limit of avoidance probabilities and
uses a maximum principle. The stationary existence proof uses compactness
and Cesaro averages; positivity and uniqueness follow from communication.
The closed-set recurrence proof also covers reducible chains, using a
positive coordinate of a stationary vector. These results are proved in
Lean, not assumed as a finite-chain theorem.

## Five-job certificate

These declarations are in namespace `OddCycle.FiveJob`:

| Claim | Declaration |
|---|---|
| Support is exactly all valid balanced C5 states | `mem_support_iff` |
| 180 states without repetitions | `support_size`, `support_nodup` |
| Every state has height three | `support_height` |
| Closure under every position completion with budget two | `support_closed` |
| Communication using only head completions | `head_communication` |
| Proper three-coloring of C5 | `proper_three_coloring` |
| Canonical defect exactly −1/360 | `canonical_defect` |
| Any nonzero rational rescaling fails stationarity | `canonical_scaled_not_stationary` |
| Positive integer certificate, exact total, every balance equation | `certificate_positive`, `certificate_total`, `certificate_stationary` |
| Normalized rational certificate is positive, sums to one, and is stationary | `probability_positive`, `probability_sum`, `probability_stationary` |
| Certificate cannot factor as K A(c) B(d), even after normalization | `normalized_certificate_not_product` |

The factorization theorem quantifies over every characteristic-zero field,
including real-valued factors. The finite stationary certificate and its
normalization are checked over the rationals, at rates (2,1,1,1,1).

## Definitions, proof organization, and trust

- `Model.lean` defines the transition rule, fixed population, placement
  orientations, balancedness, directed-path height, canonical prefix
  weights, and row-generator balance.
- `Operational.lean`, `EdgeOrder.lean`, and `PlacementOrder.lean` establish
  population preservation and the edge-order invariant. The cycle geometry
  and symmetry modules lead to `GeneralClosure.lean` and `GeneralHeight.lean`.
- `Reachability.lean`, `WordCommunication.lean`, `BalancedMoves.lean`, and
  `GeneralCommunication.lean` construct actual completion paths.
- `Interleavings.lean`, `BranchChains.lean`, `BalancedWords.lean`, and
  `GeneralCardinality.lean` count the original balanced state space.
- `BudgetStability.lean`, `ChangedEvents.lean`, `InterleavedCarry.lean`,
  `ArcCarry.lean`, and `ChangedReconstruction.lean` characterize and invert
  changed events. `FlowWords.lean`, `FlowWordLabels.lean`, and
  `TwoFlowCompleteness.lean` identify the two sources.
- `EventWeights.lean`, `IncomingOccurrences.lean`, and `TwoFlowBalance.lean`
  preserve event multiplicities when comparing balance equations.
  `UnlimitedCarry.lean` and `UnlimitedPredecessors.lean` reconstruct all
  unrestricted incoming events. The target modules culminate in
  `UnlimitedTargetBalance.lean`.
- `PrefixWeights.lean`, `UniformWeights.lean`, `FactorialProducts.lean`,
  `UniformDefect.lean`, `DefectSign.lean`, and `UniformObstruction.lean`
  evaluate the general formula and its consequences.
- The `FiniteMarkov`, `FiniteReturn`, `FiniteStationary`,
  `StationaryExistence`, `FiniteRecurrence`, and `ClosedRecurrence` modules
  prove the finite probability results. `QueueMarkov.lean`,
  `QueueStationary.lean`, and `BalancedRecurrence.lean` connect them to the
  queue model; `PartiteColoring.lean` proves the partiteness hypothesis.
- `Certificate.lean` contains untrusted integer weights and finite path
  witnesses. `FiveJob.lean`, `Balance.lean`, and `Conclusions.lean` check the
  finite claims, normalization, and nonfactorization.
- `Audit.lean` lists the axioms used by the principal declarations.

Finite calculations use `decide +kernel`. There are no admitted proofs,
custom mathematical axioms, or native-evaluation axioms in the imported
proofs. The audit reports only `propext`, `Classical.choice`, and `Quot.sound`;
some declarations require none.

The certificate does not define the state space: its support is proved
equivalent to validity and balanced orientation by checking all 720
configurations. General cardinality and closure use structural proofs,
without enumerating cycle sizes.

The Lean closure proof proceeds directly through a rank invariant and does
not use Lemma 1 of reference [1] in the paper, so it constitutes an independent
proof. The general balance proof likewise verifies unlimited balance at the
target directly, without assuming the cited unlimited product-form theorem.

## Scope boundary

The newer complete-cycle classification is developed in
`OddCycle/CycleClassification.lean`; its theorem map is in
[CYCLE_CLASSIFICATION.md](CYCLE_CLASSIFICATION.md). The arbitrary-size
operational classification, exceptional-class uniqueness and exact orientation
count, positive-position completion kernel, recurrence and absorption, general
OI canonical stationarity, and sharp product-form boundary are checked.
The larger-cycle unit-rate residual includes complete predecessor counting and
actual exceptional-class membership. C9/w=2 is an explicit checked specialization.

Recurrence and absorption hold on the explicitly constructed probability
space of continuous-time paths. The infinite completion trajectory uses
Ionescu--Tulcea; independent unit exponentials are divided by the current
state's total rate. The proof checks exponential completion probabilities,
measurability, nonexplosion, legal transitions, and transfer of the finite-chain
return and avoidance formulas. Almost every path eventually stays in one
of the classified communicating classes. Stationarity uses the original
continuous-time generator's balance equations.

`CycleClassifier.classify_continuous_recurrence` connects an executable rank-array
and run classifier to this continuous-time recurrence event. Its cost is at
most `33*n + 18` units in the explicitly instrumented word-RAM model, including
placement construction and array initialization. This is an algorithmic
operation bound, not a bit-complexity or compiler wall-time guarantee.

The new working proof's reported JSON experiments are not Lean proofs; their
files were not present in this checkout and are not assumed by the theorems.

The C7 classification, small-graph screen, and other finite experiments in
the manuscript are verified by the Python suite, not by these Lean proofs.
The manuscript as a whole should therefore not be described as fully
formalized.
