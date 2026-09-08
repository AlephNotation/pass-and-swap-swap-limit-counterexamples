# Verification report

The `excess-edge-introduction` revision is an editorial follow-up to v1.3.
It rewrites the introduction, clarifies reversible transport and the general
orientation-ring consequence in Section 3, and updates the theorem map.

The Lean and Python sources, exact certificates and expected results,
manuscript statement checks, toolchain, and CI settings are identical to
`4399043ad938a4faec51726acca731f25e7a4845`. That commit passed the
[complete CI run](https://github.com/AlephNotation/pass-and-swap-swap-limit-counterexamples/actions/runs/34171095333):
the full Lean build, manuscript declarations, all five axiom audits, full
kernel replay, both certificate exports, and all eight Python components.
The [v1.3 report](https://github.com/AlephNotation/pass-and-swap-swap-limit-counterexamples/blob/v1.3/verification/REPORT.md)
retains the earlier local build and certificate-regeneration records.

Local editorial checks completed on 7 September 2026:

| Check actually run | Result |
|---|---|
| Two `tectonic --keep-logs --keep-intermediates --outdir DIR paper.tex` builds | Passed; 17 pages, no TeX warnings or box problems |
| `pdftoppm -r 100 -png DIR/paper.pdf DIR/page` and visual inspection | All 17 pages reviewed; enlarged inspection of the introduction, ring argument, and final page |
| Source comparison of all theorem, lemma, proposition, corollary and abstract environments | Unchanged from v1.3; author and assistance acknowledgment also unchanged |
| Label/reference check | 48 unique labels; all 57 internal references resolve |
| Git comparison of proof, verifier, data, expected-result and build inputs | Identical to the green v1.3 commit |
| `git diff --check` | Passed |

No Lean build, kernel replay, or Python verification suite was rerun locally
for this prose-only change. The [CI workflow](https://github.com/AlephNotation/pass-and-swap-swap-limit-counterexamples/actions/workflows/lean.yml)
records results for the new commit separately; the baseline run above is
identified explicitly rather than reported as a new run.

The introduction distinguishes universal canonical validity from stationarity
for a particular allocation. The unit-rate C5 control and the balanced-family
checks at `w=2,3,4,5` remain exact finite computations. The bidirectional ring
for every `k >= 1` is presented as a consequence of the proved move rule and
parameterization, not a separately packaged Lean graph-isomorphism theorem.
[LEAN.md](../LEAN.md) gives the statement map and precise scopes.

No generated verification logs are tracked. [PACKAGE.md](../PACKAGE.md)
documents optional complete replay, file hashes, and source packaging.
