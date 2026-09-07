# Verification report

Checked source commit: **`d29d76295f71b441271695138dc134463afc5df7`**. The run completed
at `2026-09-07T22:23:24.096180+00:00` with **PASS**; all 198 recorded input hashes
remained unchanged. Subsequent changes affect verification packaging and
documentation, this report, and restoration of the DOI badge. The manuscript,
Lean proofs, numerical verifiers, certificates, and expected results are unchanged.
A later repeat was interrupted at the user's request and is not reported as passed.

```sh
LEAN_NUM_THREADS=1 /opt/homebrew/opt/python@3.14/bin/python3.14 -B code/verify_release.py --output-dir /var/folders/mh/_6j73xhj1ms1576h946m7vxw0000gn/T/cycle-editorial-verification-b_2zxi58
```

| Check actually run | Result |
|---|---|
| `lake build` and manuscript signature check | Passed; full default build |
| All four Lean axiom audits | Passed; 59 / 125 / 34 / 40 declarations; only standard logical axioms |
| `lake env leanchecker --verbose OddCycle` | Passed; all 158 project modules replayed |
| `run_checks.py`, normally and under `-O` | Passed; all seven expected result files reproduced |
| Lean certificate export, stationary regeneration and independent verification | Passed; regenerated certificate exactly matches committed data |
| Two Tectonic builds, internal references and page-render comparison | Passed; no warnings or box problems; all 15 pages match |

Tools: Lean (version 4.28.0, arm64-apple-darwin24.6.0, commit 7e01a1bf5c70fc6167d49c345d3bf80596e9a79b, Release); Python 3.14.6; Tectonic 0.17.0; pdftoppm version 26.08.0.

All 15 manuscript pages were visually inspected. The full name **Tynan Daly**
appears in the paper and PDF metadata. The acknowledgment is unchanged.
The finite-results section and Appendix A are about one third shorter.
Every Lean proof source and the original certificates, graph inputs, and
six earlier result files remain unchanged from `db64de0cda584d7a7cf971d75696b786c966ea06`.

The [theorem map](../LEAN.md) records exact assumptions. The new Conjecture 1
corollary distinguishes failure at exceptional lengths for **every admissible
OI allocation** from validity at other lengths under **positive position
rates**. This differs from canonical failure, which is an existence statement
about allocations. Seven additional complete head-only checks find no tall
recurrence; removing positivity from the general validity direction remains
open. These computations do not replace the Lean classification.

`verification/` tracks only this report and `ManuscriptStatements.lean`.
The GitHub release supplies the completed run's command/status logs, input
hashes, regenerated outputs, rendered pages, and review records as a separate
verification-evidence archive, identified by the checked commit above. GitHub
source archives contain the released source revision. Generated evidence stays
out of the repository. [PACKAGE.md](../PACKAGE.md) explains how to regenerate
a consolidated package from a matching source revision and successful run.
