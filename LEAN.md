# Lean verification and manuscript theorem map

The main entry point is `OddCycle.CycleClassification`, imported by the
default `OddCycle` build. It proves the arbitrary-size recurrent-class
classification and sharp canonical product-form boundary for the actual
two-queue completion rule. Existing balanced-family, finite-certificate,
structural, and continuous-time path-law proofs remain included.

The source statements, rather than the manuscript wording, determine the
assumptions. Unless a row gives a different namespace, declarations below
are prefixed by `OddCycle.`. Paper references use stable LaTeX labels;
the PDF supplies their displayed numbers. `verification/ManuscriptStatements.lean`
prints the key structures and exact theorem signatures; its output is retained
in `verification/manuscript-statements.log`.

## Main theorem map: assumptions and scope

| Manuscript claim / label | Actual declarations | Exact scope |
|---|---|---|
| Complete recurrent classification (`thm:classification`) | `CycleState.terminal_iff_runs`; `PositivePositionAllocation.continuous_recurrent_iff_runs` | Valid states on `C_n`, `n >= 3`, `w >= 1`; stochastic statement requires positive finite rates at every occupied position. No OI assumption. |
| Complete list of closed classes | `closed_class_classification`; `ClosedClass.short_fiber`; `ClosedClass.exceptional_family` | `ClosedClass n w states` means a nonempty duplicate-free list, valid states, closure under every completion, and event communication. Positivity identifies these with stochastic closed classes. Lists are compared up to permutation. |
| Tall-class existence and uniqueness | `exists_tall_terminal_iff`; `exceptionalStates_closedClass`; `exceptionalRuns_communicate` | `n >= 3`, `w >= 1`; exists iff `n=2kw+1`, `k >= 1`. All exceptional configurations, not only representatives, communicate. |
| Exactly `2n` exceptional orientations | `exceptionalParameter_covers`; `exceptionalParameter_injective`; `exceptional_orientation_count` | Actual labeled orientations at exceptional lengths. This counts orientations, not full configurations. |
| Closure under nonnegative allocations | `exceptionalRuns_transition`; `CycleState.exceptional_recurrent_state` | Operational closure has no rate assumption. The recurrence-existence theorem allows only legal events or self steps in an arbitrary finite kernel. This does not prove general irreducibility with zero non-head rates. |
| Eventual residence in one class | `PositivePositionAllocation.continuous_eventually_one_class` | Same positive-position hypotheses; almost-sure event on the constructed physical-time path space. |
| Same-orientation communication (`lem:fiber`) | `reachable_of_orientation_eq`; `CycleState.orientation_reachable_iff`; `ReachabilityQuotient.reach_iff` | Actual zero-replacement paths between valid configurations, all cuts and linear extensions; positivity makes the paths available. |
| Exact operational/path-flip equivalence (`lem:local`) | `transition_changed_path`; `cycle_path_realize_flip`; `orientationStep_iff_pathFlip`; `orientationStep_iff_circularFlip` | `n >= 3`, `w >= 1`; existence of a nontrivial quotient edge, not an orientation Markov kernel. |
| Run classification (`sec:runs`) | `CircularRun.terminal_iff`; `CircularRun.exceptional_iff_one_long`; `BinaryCycle.terminal_iff`; `CycleState.terminal_iff_runs` | The run relation is proved equivalent to the original quotient; recurrence is not defined to mean the proposed run test. |
| Positive canonical law (`cor:positive`) | `unlimited_oi_stationary`; `short_class_normalized_oi`; `ClosedClass.safe_normalized_oi` | `n >= 3`, `w >= 1`, `n % (2*w) != 1`; each queue has its own `PositiveOIAllocation n`. Normalization, positivity, and original generator balance are proved. |
| Sharp universal boundary (`thm:sharp`) | `cycle_canonical_sharpness`; **`cycle_normalized_canonical_sharpness`** | **`n >= 3`, `w >= 2`**. Quantifies over every pair of positive OI allocations and every actual closed class. Equivalence is with universal validity, not allocation-specific validity. |
| Balanced case is the first exceptional class | `balanced_is_exceptional`; `balanced_cardinality` | `w >= 2`; `B_w=T_(2w+1,w)`; `2(2w+1)(2w+2) choose(2w-1,w)` full states. |
| Uniform two-flow obstruction (`thm:balanced`, `lem:two`) | `two_flow_completeness`; `uniform_two_flow_identity`; `uniform_defect`; `uniform_defect_pos`; `uniform_defect_neg`; `uniform_defect_two` | `w >= 2`; same additive rates in both queues, `r_0=theta>0`, other rates 1; exact defect nonzero iff `theta != 1`. At 2 it is `-w/(2w+2)!`. Zero at the displayed target when theta=1 is not a full all-w stationarity proof. |
| Unit-rate larger family (`thm:unit`) | `unit_target_orientation`; `unit_gain_exceptional`; `unit_gained_predecessors`; `unit_lost_predecessors`; **`unit_exceptional_residual`** | `w >= 1`, `k >= 2`, `n=2kw+1`; unit position rates; on `exceptionalStates n w`; target uses the constructed `unitInterior n w k`. Residual `[1-2w(k-1)]/n!` includes complete predecessor counting and support membership. |
| Explicit C9 (`eq:nine`) | `NineJobCycle.target_member`; `NineJobCycle.recurrent_class`; `NineJobCycle.gained_event`; `NineJobCycle.residual` | `n=9`, `w=2`, unit position rates; target `([0],[7,8,6,3,4,5,2,1])`; unnormalized defect `-1/120960`. No enumeration needed for the Lean specialization. |
| Five-job four-predecessor result (`sec:five`) | `FiveJob.canonical_defect`; `FiveJob.canonical_scaled_not_stationary` | `n=5`, `w=2`, additive rates `(2,1,1,1,1)` in each queue. Complete table also reconstructed by `verify_five.py`. |
| Exclusion of all queue-wise factors (`prop:nonfactor`) | `FiveJob.certificate_stationary`; `FiveJob.certificate_total`; `FiveJob.normalized_certificate_not_product` | Exact C5 allocation above. Nonfactorization over every characteristic-zero field, including real factors. Not a theorem for all exceptional cycles. |
| Head-only communication (`prop:heads`) | `FiveJob.head_communication`; `FiveJob.support_closed` | `n=5`, `w=2`; any allocation retaining positive heads, including all admissible OI allocations. The nine-orbit table and uniform law at equal unit head rates are separately checked in Python. |
| Partiteness | `partiteColor_proper`; `partiteColor_surjective` | `C_(2w+1)`, `w >= 2`, exactly `w+1` nonempty colors. Odd cycles at `w=1` are not bipartite and do not refute Conjecture 1 under its hypothesis. |
| Linear executable recurrence test | `CycleClassifier.classify_correct`; `CycleClassifier.classify_cost`; `CycleClassifier.classify_continuous_recurrence` | Valid state, `n >= 3`, `w >= 1`; bound `33*n+18` in the instrumented bounded-word RAM model, not bit complexity or measured runtime. |

`PositiveOIAllocation n` is an OI capacity (permutation-invariant total rate,
zero empty capacity) with positive prefix increments on every valid queue
prefix. Its values and the two queues' allocations need not coincide.
`oiBalance_eq_positionGenerator` identifies OI balance with the actual
position-event generator including diagonal subtraction. The short-class
proof establishes unlimited balance by complete incoming scan inversion and
telescoping prefix weights. No publisher theorem is introduced as an axiom.

## Quantifier and evidence checks made during consolidation

- Kept `w >= 1` for recurrence and safe-length sufficiency; retained **`w >= 2`**
  for the sharp universal equivalence. No claim is made to settle its omitted
  one-swap cases or the arbitrary-graph bipartite conjecture.
- Distinguished structural closure for nonnegative allocations from
  irreducibility under positive position rates; the C5 head-only result has
  its own stronger support hypothesis.
- Restricted all-factor nonfactorization to the explicit C5 certificate.
- The family unit-rate residual uses a particular interior order constructed
  in Lean. The paper fixes that construction; it does not attribute an extra
  universally quantified theorem over arbitrary interior words to Lean.
- Removed class asymmetry as a general explanation of failure. Unit rates
  already fail on the larger exceptional family.
- The publisher's Theorem 7 also states a partiteness hypothesis. The general
  short-class argument is derived from unlimited Theorem 3 and proved
  independently in Lean, so it does not import an unstated partite assumption.

## Separately computed results

| Claim | Packaged check / expected result | Scope |
|---|---|---|
| C5 and C7 full state counts, terminal SCCs under heads and all positions | `verify_classification.py` / `results/classification.json` | C5/w2: 720 states, 180 tall recurrent; C7/w3: 40,320 states, 1,120 tall recurrent. C7 has 3,248 height-four states, of which 2,128 are transient. |
| Uniform-formula balanced-region controls | `verify_uniform.py` / `results/uniform.json` | Entire `B_w` at w=2,3,4,5, theta=1/2,1,2,3; source words through w=50. Canonical balance at theta=1 is computational evidence only on this tested part of **n=2w+1**. |
| C9 complete exceptional-class enumeration | `verify_nine.py` / `results/nine_job.json` | 131,040 states, 18 orientations, 1,179,360 events per generator; 16,560 nonzero limited residuals, zero unlimited residuals, target -3 in integer scaling. |
| Five-job certificate and orbit table | `verify_five.py`, `verify_orbits.py` / corresponding JSON | Exact 180-state certificate, 45 representative events, 72,000 symmetry identities, unit-head balance. |
| Small-graph screen | `verify_screen.py` / `results/screen.json` | All 61 simple bipartite graphs on 1..6 vertices at w=1; four named graphs at w=2; 192,590 states, 1,143,194 all-position events. |

The general classification is proved in Lean; its computed state counts
are not thereby claimed as separate formal cardinality theorems. The older
working note mentioned `cycle_checks.json`, `symmetric_checks.json`, and
`nine_job_checks.json`, which were absent from this checkout. They have not
been represented as supplied or replayed. The new `results/nine_job.json`
is a fresh complete reproduction of the stated C9 experiment. The unavailable
65-parameter quotient and 32-pair source-word reports are not paper evidence.

## Build, axiom audits, and kernel replay

The [Lean proofs workflow](.github/workflows/lean.yml) runs the full default
build, manuscript statement checks, all four audits, full-root kernel replay,
and the generated-certificate consistency check on pushes and pull requests.
It also supports manual runs. `python3 -B code/check_axioms.py` runs and
validates all four audits locally; CI and the release verifier share its
allowlist validation. A missing audit output, failed Lean command, or axiom
outside `propext`, `Classical.choice`, and `Quot.sound` fails the check.
The audit scope is the declarations listed in those four audit modules;
kernel replay covers the full `OddCycle` library. CI sets
`LEAN_NUM_THREADS=1` for kernel replay to bound Mathlib memory use.

```sh
lake exe cache get
lake build
lake env lean OddCycle/Audit.lean
lake env lean OddCycle/CycleClassificationAudit.lean
lake env lean OddCycle/StructuralTheoryAudit.lean
lake env lean OddCycle/IndistinguishabilityAudit.lean
lake env leanchecker --verbose OddCycle
python3 -B code/export_lean_certificate.py --check
```

The cache command is first-install setup. The full replay includes all
imported project modules, including the preserved mixing lemmas. Audits
permit only `propext`, `Classical.choice`, and `Quot.sound` (or fewer);
finite reductions use `decide +kernel`. There are no admitted proofs,
custom axioms, or native-evaluation axioms. Actual commands and outcomes
for this revision are in [verification/REPORT.md](verification/REPORT.md),
with machine-readable logs and source hashes. [PACKAGE.md](PACKAGE.md)
documents regeneration of the whole verification package.

## Detailed balanced-family declarations

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
| Balanced communication with positive position rates explicit | `balanced_positive_rate_communication` |
| Proper coloring using exactly w+1 nonempty colors | `partiteColor_proper`, `partiteColor_surjective` |
| Only full-queue head events can change with the budget | `balanced_changed_event_head` |
| Unique source reconstruction for a changed incoming event | `balanced_changed_head_injective` |
| Exactly the gained X and lost Y changed events | `two_flow_completeness` |
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

Balanced closure has no rate assumptions:
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


## Exact queue-length indistinguishability

Fix `w >= 1`, `k >= 2`, and `n=2kw+1`. Use one distinct job per vertex of
`C_n`, with edges `{i,(i+1) mod n}`. Every occupied position in both queues has
rate one: the OI capacities are `mu(q)=nu(q)=|q|`. The budget allows `w`
replacements after an initiating completion. The support is the proved
closed communicating class `C=T_(n,w)`, with one circular orientation run of
length `w+1` and the other `2k-1` runs of length `w`.

Let `W(c,d)=1/(|c|! |d|!)`, `Z_C=sum_{s in C} W(s)>0`, and
`hat_pi=W/Z_C`. The declaration
`OddCycle.unit_exceptional_queue_length_indistinguishability` proves together:

- `hat_pi` is a probability vector and is not invariant under the actual
  completion kernel.
- A stationary comparison vector `pi` exists on that same class. Under `pi`,
  the full configuration distribution remains `pi` at every physical time.
- The entire continuous-time queue-length trajectory has the same law under
  `hat_pi` and `pi`, as an equality of measures on `NNReal -> Nat` with its
  coordinate-generated sigma algebra.
- For `D=hat_pi Q`, every length fiber has zero total residual, while the
  explicit family target has residual `[1-2w(k-1)]/(n! Z_C)<0`.

Thus every measurable test based only on queue-length observations has the
same distribution under these two initializations. The proof uses the existing
queue process and exponential clocks, and connects the original OI residual
to the actual completion-kernel residual.

For the explicit `C9`, budget `w=2`, all rates one, the target is
`((0),(7,8,6,3,4,5,2,1))`. It lies in `T_(9,2)`, with circular run lengths
`3,2,2,2`. Its unnormalized residual is `-1/120960`, and its normalized
residual is `-1/(120960 Z_C)`. The concrete declaration is
`OddCycle.NineJobCycle.queue_length_indistinguishability`.

```sh
lake build
lake env lean OddCycle/IndistinguishabilityAudit.lean
lake env leanchecker OddCycle.QueueLengthIndistinguishability
```

The consolidation's full build, axiom counts, and kernel replay are recorded
in `verification/REPORT.md`. No proof statement in this extension was changed
for the manuscript rewrite.

This theorem gives no quantitative convergence time. The separate balanced-family
slow-mixing proof still needs the operational symmetry and half-arc flow count,
the length coupling estimate, and the identification of the Poisson-averaged
law with the existing clocked process. Its full-queue obstruction is not
transferred to the larger exceptional families here.


The queue-length result is a consequence of autonomous aggregate rates and
equal-cut counting. Its measure-theoretic implementation does not supply a
mixing-time bound. The original balance residual, rather than only an
embedded-kernel defect, is identified in `ClosedClass.unit_balance` and
`ClosedClass.unitCanonical_residual_by_length`.

For full continuous-time recurrence, `MarkovPathMeasure` constructs infinite
completion trajectories by Ionescu--Tulcea. `ExponentialClocks` constructs
independent unit exponential clocks, proves positivity and divergence, and
restricts to their measure-one good set. `ClockedPath` divides these clocks
by each state's total rate; finiteness and positivity imply nonexplosion.
`TimedJumpLaw` verifies the waiting-time and destination laws, and
`CycleContinuousTime` proves recurrence and eventual residence in one class.
Return is after the first completion epoch, excluding the initial holding
interval. General stationary assertions use the original continuous-time
generator, not an unadjusted embedded-chain stationary vector.

The exact generator identities for position-indexed or length-dependent
capacities are `lengthGenerator_eq`, `lengthGenerator_budget_independent`,
and `capacity_lengthGenerator`. Equal-cut counting and canonical marginals
are `ClosedClass.wordCutEquiv`, `normalized_length_marginal`, and
`canonical_length_marginal`. The explicit nonstationarity/path-law family
retains unit rates and `k >= 2`; no broader failure example is inferred.

## Preserved unfinished work

The default build still includes all structural, finite-bottleneck, and
Poisson-evolution modules. [docs/FUTURE_WORK.md](docs/FUTURE_WORK.md) lists
their exact completed scope and the missing obligations for a quantitative
continuous-time mixing theorem. No such theorem is a manuscript claim.
