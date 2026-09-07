# What a finite replacement budget changes

Working extension, 7 September 2026. The first structural results below are
formalized in `OddCycle/StructuralTheory.lean`. The continuous-time mixing
estimates have written proofs; their remaining Lean obligations are listed
explicitly below. This extension has not received independent review and is
separate from the consolidated manuscript. No priority claim is made.

The distinction is between population movement and job order. A completion
always transfers one job to the other queue. A finite replacement budget can
change which job moves, the placement orientation, the recurrent classes, and
the joint stationary law, while leaving the entire queue-length process
unchanged under the allocations considered here.

## 1. An autonomous queue-length process

Use the original first-later-compatible rule, with `w` counting replacements,
and put `K=|c|`. Give zero-based position `p` rate `a_p` in the first queue and
`b_p` in the second, independently of the labels. Assume finite, nonnegative,
time-homogeneous rates. For any swapping graph and any budget, including zero,
the generator on a function of queue length is

\[
 Q(f\circ K)(c,d)
 =\left(\sum_{p<K}a_p\right)[f(K-1)-f(K)]
 +\left(\sum_{p<n-K}b_p\right)[f(K+1)-f(K)].
\]

Every occupied first-queue position contributes to the same downward change;
every occupied second-queue position contributes to the same upward change.
There are no other changes of `K`. This proves the generator identity directly
from actual completion events. The aggregate rates depend only on `K`, so the
finite continuous-time chain projects to this birth–death process. In
particular, its law given the initial queue length does not depend on the
swapping graph or budget.

For OI capacities `mu(q)=A_|q|`, `nu(q)=B_|q|`, with `A_0=B_0=0`, the position
rates are `A_(p+1)-A_p` and `B_(p+1)-B_p`. Telescoping gives

\[
 k\longrightarrow k-1\quad\text{at rate }A_k,
 \qquad k\longrightarrow k+1\quad\text{at rate }B_{n-k}.
\]

Strictly positive prefix increments give an admissible positive-position OI
allocation. The Lean development constructs that allocation and proves the
event-level generator identities. The general passage from a generator
identity to equality of projected continuous-time path laws is not yet
formalized in this extension.

## 2. Correct length marginals can conceal incorrect joint weights

Assume positive position service and fix any closed communicating class `C`.
Tail completions move the cut of `L=c ++ reverse(d)` without changing `L`.
Consequently, if a placement word occurs in `C`, all its `n+1` cuts occur in
`C`. Each word has exactly one cut at each queue length. If `M_C` is the number
of placement words in the class, then

\[
 |\{s\in C:K(s)=k\}|=M_C\qquad(0\le k\le n).
\]

In particular, this count is independent of `k`, even when `C` contains many
orientations. Lean proves an explicit equivalence between the class and its
placement words times `Fin(n+1)`. Its closed-class interface here is the
existing cycle interface; the underlying tail-completion argument works on
any swapping graph.

For capacities determined by length, define

\[
 R_k=\prod_{i=1}^{k}A_i^{-1}
     \prod_{j=1}^{n-k}B_j^{-1},\qquad
 \rho_k=\frac{R_k}{\sum_{\ell=0}^{n}R_\ell}.
\]

The canonical weight of a state is exactly `R_K`. The equal cut counts cancel
from its normalization, giving the length marginal `rho` on every class.
Moreover,

\[
 R_k B_{n-k}=R_{k+1}A_{k+1}\qquad(0\le k<n),
\]

so `rho` is the stationary law of the irreducible length process. This yields
three distinct conclusions:

- The true stationary law of the full class has length marginal `rho`.
- The normalized canonical weights also have length marginal `rho`, whether
  or not they are stationary jointly.
- Starting the full process from those canonical weights gives a stationary
  queue-length process, even if the full configuration law subsequently moves.

Lean proves the canonical marginal identity, positivity and normalization of
`rho`, the detailed-balance identity, and zero expected generator for every
function of queue length. The process-law conclusions also use the
continuous-time projection step identified in Section 1.

The distinction occurs in the already proved unit-rate counterexamples:
for every `w >= 1`, `k >= 2`, `n=2kw+1`, on `T_(n,w)`,

\[
 WQ\ne0,\qquad
 \sum_{s\in T_{n,w}} W(s)Q(f\circ K)(s)=0
 \quad\text{for every }f.
\]

These two statements are proved together in
`unit_exceptional_hidden_defect`. At unit rates `A_i=B_i=i`, the common length
marginal is `Binomial(n,1/2)`. Thus the C9/w=2 canonical defect can be invisible
to every statistic of the queue-length process. This is a failure of those
observations to determine joint stationarity, not an alternative full
stationary formula.

## 3. Slow orientation changes on the balanced family

Now restrict to `B_w=T_(2w+1,w)`, `w >= 2`, and retain capacities determined by
length with strictly positive prefix increments. Let `pi` be the unique full
stationary law, and let `g(s)` be the total rate of orientation-changing
events from `s`.

The existing changed-event theorem, compared with an unlimited completion,
implies that an orientation change must complete the head of a queue
containing every job. There is at most one such initiating position. Therefore

\[
 g(s)\le A_1\mathbf1_{K(s)=n}+B_1\mathbf1_{K(s)=0},
 \qquad \pi(g)\le\gamma:=A_1\rho_n+B_1\rho_0.
\]

The operational necessity and uniqueness of this position are proved in
`BalancedBottleneck.lean`. This full-queue restriction has not been established
for the larger exceptional families with `k>1`; the bound below is for `B_w`.

Rotation and reflection of labels preserve the actual generator and `K`.
Uniqueness makes `pi` invariant under these relabelings. Their action is
transitive on the `2n` balanced orientations, so orientation is uniform
conditional on each queue length.

The orientation transition support is the bidirectional cycle `C_(2n)`.
This support statement does not assert a Markov projection onto orientations.
For every `j` modulo `2n`, let `E_j` contain the `n` consecutive orientation
fibers beginning at `j`. Each has stationary mass `1/2`. Define its stationary
outward flow by

\[
 F(E)=\sum_{x\in E,\ y\notin E}\pi(x)Q(x,y).
\]

Every directed edge of the orientation cycle exits exactly one of these
`2n` half-arcs. An event preserving orientation exits none. Hence

\[
 \sum_j F(E_j)=\pi(g).
\]

Choose `E` with `F(E)<=pi(g)/(2n)` and start from `eta=pi(.|E)`. Conditional
uniformity leaves its length marginal equal to `rho`, so its length process
is stationary. Also `eta P_t<=2pi`. The expected number of exits from `E`
by time `t` is at most `2tF(E)`. Being outside `E` requires an exit, giving

\[
 \|\eta P_t-\pi\|_{TV}
 \ge\tfrac12-2tF(E)
 \ge\tfrac12-\frac{t\pi(g)}n
 \ge\tfrac12-\frac{t\gamma}n.
\]

Convexity transfers this mixed-start bound to worst-case deterministic starts:

\[
 t_{\rm mix}(\text{full},1/4)\ge\frac{n}{4\gamma}.
\]

No reversibility or explicit full stationary formula is needed. The general
stationary-flow method is standard; see
[Levin–Peres–Wilmer, Section 7.2 and Chapter 20](https://www.stat.berkeley.edu/~aldous/260-FMIE/Levin-Peres-Wilmer.pdf).
The queue application and half-arc averaging above are the present argument.

For constant per-position rates `alpha>0` and `beta>0`, write
`p=beta/(alpha+beta)`. Then `rho=Binomial(n,p)` and

\[
 \gamma=\alpha p^n+\beta(1-p)^n.
\]

The length process is the number of occupied bits in `n` independent two-state
chains with upward rate `beta` and downward rate `alpha`. Refreshing each bit
at rate `alpha+beta`, with fresh value `Bernoulli(p)`, couples any two starts
once every bit has refreshed. Thus

\[
 t_{\rm mix}(K,1/4)\le\frac{\log(4n)}{\alpha+\beta},
 \qquad
 t_{\rm mix}(\text{full},1/4)
 \ge\frac{n}{4[\alpha p^n+\beta(1-p)^n]}.
\]

At unit rates these become

\[
 \boxed{t_{\rm mix}(K,1/4)\le\tfrac12\log(4n),\qquad
 t_{\rm mix}(\text{full},1/4)\ge n2^{n-3}.}
\]

Time is physical continuous time with each occupied position completing at
rate one. The full-chain lower bound improves the supplied research-ladder
bound by a factor of `2n`. Exponential growth for unequal rates assumes fixed
positive `alpha,beta`; it is not uniform over rate ratios varying with `n`.

## 4. Exact formalization scope

Entry point: `OddCycle/StructuralTheory.lean`. All names below are in `OddCycle`.

| Proved result | Principal declaration |
|---|---|
| Actual completion changes first-queue length by exactly one | `transition_first_length` |
| Generator on lengths for arbitrary position-indexed rates | `lengthGenerator_eq` |
| Independence of swapping graph and budget | `lengthGenerator_budget_independent` |
| Positive OI allocation from strictly increasing length capacities | `positiveByLengthAllocation` |
| OI birth–death generator | `capacity_lengthGenerator` |
| Class equals placement words times cuts | `ClosedClass.wordCutEquiv` |
| Equal weighted sums at each cut | `ClosedClass.length_weight_at` |
| Canonical length marginal on every cycle class | `ClosedClass.canonical_length_marginal` |
| Positive normalized length law | `lengthLaw_simplex` |
| Birth–death detailed balance | `lengthCanonical_detailed_balance` |
| Canonical balance for all length observables | `ClosedClass.canonical_length_observables` |
| Full canonical failure coexists with all length balance identities | `unit_exceptional_hidden_defect` |
| Orientation change requires a full-queue head completion | `balanced_orientation_change_boundary` |
| At most one orientation-changing initiating position per state | `balanced_orientation_change_unique_position` |
| Discrete finite-kernel stationary-flow bound | `FiniteMarkov.bottleneck_lower` |
| Convexity transfers mixed-start bounds to point starts | `FiniteMarkov.totalVariation_mixture` |
| Poisson-averaged laws are probability vectors | `FiniteMarkov.poissonEvolve_simplex` |
| Stationary-flow bound after Poisson averaging | `FiniteMarkov.poisson_bottleneck_lower` |

The full continuous-time queue mixing estimate is **not yet a Lean theorem**.
Remaining obligations are: stationary invariance under the operational label
symmetries and conditional orientation uniformity; the half-arc exit-count
identity; the length coupling estimate; and the connection between
`poissonEvolve` and the existing exponential-clocked process at constant total
rate. The more general length-capacity process statement also needs a
continuous-time projection theorem. None of these obligations is installed as
an axiom or as a hypothesis concealing the desired queue mixing conclusion.

Verification:

```sh
lake build
lake env lean OddCycle/StructuralTheoryAudit.lean
lake env leanchecker OddCycle.StructuralTheory
```

Verified on 7 September 2026: the full build completed successfully (3002 jobs),
all 34 audited declarations depend only on `propext`, `Classical.choice`, and
`Quot.sound` (or a subset), and kernel replay exited successfully. There are
no proof holes or added axioms in this extension.

The next quantitative step is to discharge these bridges and obtain the boxed
mixing separation for the existing continuous-time queue process. Extending
the bottleneck geometry to `T_(2kw+1,w)` with `k>1` is a separate mathematical
question; the recurrence classification alone does not supply a mixing bound.
