# Verification report

Revision: the `even-cycles-modulated-budget` branch. The
[Lean proofs workflow](https://github.com/AlephNotation/pass-and-swap-swap-limit-counterexamples/actions/workflows/lean.yml)
records the exact commit SHA and full machine-proof results for every push.
The checks below completed locally on 7 September 2026 before committing
this revision.

| Command actually run | Result |
|---|---|
| `LEAN_NUM_THREADS=1 lake build` | Passed; full default build, 3,018 jobs, including the new stationary-law theorem |
| `LEAN_NUM_THREADS=1 lake env lean verification/ManuscriptStatements.lean` | Passed; manuscript declarations and signatures checked |
| `LEAN_NUM_THREADS=1 python3 -B code/check_axioms.py` | Passed; all five audits, 59 / 125 / 34 / 40 / 20 declarations; only `propext`, `Classical.choice`, and `Quot.sound` |
| `python3 -B run_checks.py` | Passed; all eight expected result files reproduced |
| `python3 -B -O code/verify_modulated.py` | Passed; optimized output equals the expected modulated result |
| `python3 -B code/regenerate_modulated_certificate.py --output data/modulated_certificate.json` | Passed; generated exact positive weights and independently verified all 360 states and 2,160 events |
| `python3 -B code/export_lean_certificate.py --check` | Passed; original certificate export unchanged and consistent |
| `python3 -B code/export_modulated_certificate.py --check` | Passed; new Lean data matches the integer certificate |
| Two complete `tectonic --keep-logs --keep-intermediates --outdir DIR paper.tex` builds | Passed; no warnings or box problems, all internal references resolve |

The final PDF has 16 pages. Rendered pages were visually inspected, including
both new statements and the certificate calculation. The author is **Tynan
Daly**; the assistance acknowledgment is unchanged.

The even-cycle result assumes positive service at every occupied position;
its canonical-law conclusion additionally assumes positive OI allocations.
The new modulated example fixes C5, budgets two/unlimited, class rates
`(2,1,1,1,1)` in both queues, and independent switching at rate one each way.
Lean proves the actual generator's unique stationary probability law and
excludes arbitrary real queue factors even when they depend on the mode.
[LEAN.md](../LEAN.md) gives the exact declaration map and scope.

Full independent kernel replay was not repeated locally for this change.
CI runs `lake env leanchecker --verbose OddCycle`, alongside the full build,
all five audits, both certificate-export checks, and the complete Python
suite. Its result must be read for the particular commit; a passing earlier
run is not evidence for a later revision. No generated verification bundle
is tracked. [PACKAGE.md](../PACKAGE.md) documents optional complete local
replay, regeneration, file hashes, and source packaging.
