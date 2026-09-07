# Consolidated verification report

The revised manuscript is organized around the complete cycle classification
and sharp universal canonical boundary. The reviewed PDF has 15 pages.
The theorem and assumption map is [LEAN.md](../LEAN.md); exact printed Lean
signatures are in [manuscript-statements.log](manuscript-statements.log).

## Revision checked

- Branch: `cycle-classification-manuscript`, created from `structural-mixing`.
- Exact source commit checked: **`a040ed9ffc826e487d5916c1455c191d7c1a2310`**.
- Preserved baseline: `ad70657914ff8d0a0f1d0a7748340a7287e63044`.
- Verification started: `2026-09-07T19:46:49.481644+00:00`.
- Verification finished: `2026-09-07T19:54:12.147787+00:00`.
- All **196** recorded input files matched that commit and remained
  unchanged throughout verification. Their hashes are in
  [input_sha256.json](input_sha256.json).
- The following local commit adds verification records only. The package's
  `SOURCE_COMMIT.txt` identifies that final packaged revision; its checked
  manuscript, proofs, scripts, data, and documentation are unchanged.

No mathematical definition, theorem, proof body, import, or default Lean
build target was changed. Two module comments now link to the synchronized
documentation. No tracked file was deleted; every original certificate,
graph input, and expected result is byte-identical to the baseline. See
[preservation.json](preservation.json). Unrelated `.gitignore` and `.DS_Store`
changes remain local and are not included in the commit or package.

## Changes

- Replaced the counterexample-led title, abstract, introduction, theorem order,
  and conclusion with the complete recurrence classification and its sharp
  canonical consequence. The operational quotient and run proof are written
  mathematically, with full-configuration communication distinguished from
  orientation edges and stochastic rates.
- Retained the uniform two-flow family, unit-rate larger family, explicit C9
  instance, four-predecessor calculation, five-job all-factor certificate,
  head-only argument, earlier finite classifications, and graph screen.
- Reduced queue-length indistinguishability to one short section. Preserved
  every structural/path-law proof and separated unfinished mixing work into
  [FUTURE_WORK.md](../docs/FUTURE_WORK.md).
- Synchronized the README, theorem map, classification documentation,
  publisher citation audit, package instructions, and unsent covering email.
  The assistance acknowledgment is unchanged. The public archive is unchanged.
- Added a complete exact C9 verifier and its expected result to the existing
  suite, reproducing the previously reported numerical instance.

## Results

**All requested automated checks passed.**

- Full Lean build: **3,014 jobs**.
- Four axiom audits: **59 / 125 / 34 / 40 entries**. Only `propext`,
  `Classical.choice`, and `Quot.sound` (or fewer) occur. No admitted proof or
  new axiom was introduced.
- Full-root kernel replay: exit 0; **158 project-module replay lines**.
- Complete Python suite: all six expected result files reproduced, both
  normally and under `-O`.
- Stationary certificate: regenerated, independently verified on the full
  180-state generator, and exactly equal to the committed JSON object.
  The Lean certificate export check also passed.
- C9/w2: **131,040 states**, **18 orientations**, **1,179,360 events per
  generator**; all unlimited residuals zero, **16,560** nonzero limited
  residuals, target **-3** in integer scaling, hence **-1/120960** unnormalized.
- Manuscript: two complete Tectonic builds; final log has no TeX warnings,
  overfull/underfull boxes, or unresolved references. All **15** page images
  rebuilt at 110 dpi match the supplied PDF exactly.
- Every page of the supplied PDF was visually inspected. The inspected PDF
  and page hashes match the verified artifact. The covering email's theorem,
  section, and appendix references match the compiled auxiliary file.

[checks.json](checks.json) is the machine-readable command/status record;
[visual_review.json](visual_review.json) records the page inspection;
[manuscript_review.json](manuscript_review.json) records the mathematical
claim and scope review. These are editorial checks, not external peer review.

## Actual commands and outcomes

The command orchestrating this run was:

```sh
python3 code/verify_release.py --output-dir /tmp/cycle-classification-verification
```

All commands below ran from the repository root. `python3` in this table
abbreviates the exact Python executable recorded in `checks.json`. Exit 0
means successful completion; no unrun command is listed as passed.

| Command | Exit | Seconds | Log |
|---|---:|---:|---|
| `lake env lean --version` | 0 | 3.905 | [lean-version.log](lean-version.log) |
| `python3 --version` | 0 | 0.007 | [python-version.log](python-version.log) |
| `tectonic --version` | 0 | 0.005 | [tex-version.log](tex-version.log) |
| `pdftoppm -v` | 0 | 0.007 | [poppler-version.log](poppler-version.log) |
| `lake build` | 0 | 15.419 | [lean-build.log](lean-build.log) |
| `lake env lean verification/ManuscriptStatements.lean` | 0 | 3.479 | [manuscript-statements.log](manuscript-statements.log) |
| `lake env lean OddCycle/Audit.lean` | 0 | 6.938 | [axioms-Audit.log](axioms-Audit.log) |
| `lake env lean OddCycle/CycleClassificationAudit.lean` | 0 | 25.853 | [axioms-CycleClassificationAudit.log](axioms-CycleClassificationAudit.log) |
| `lake env lean OddCycle/StructuralTheoryAudit.lean` | 0 | 6.338 | [axioms-StructuralTheoryAudit.log](axioms-StructuralTheoryAudit.log) |
| `lake env lean OddCycle/IndistinguishabilityAudit.lean` | 0 | 16.612 | [axioms-IndistinguishabilityAudit.log](axioms-IndistinguishabilityAudit.log) |
| `lake env leanchecker --verbose OddCycle` | 0 | 330.487 | [kernel-replay.log](kernel-replay.log) |
| `python3 -B run_checks.py` | 0 | 13.600 | [python-suite.log](python-suite.log) |
| `python3 -B -O run_checks.py` | 0 | 14.230 | [python-suite-optimized.log](python-suite-optimized.log) |
| `python3 -B code/export_lean_certificate.py --check` | 0 | 0.037 | [lean-certificate-export.log](lean-certificate-export.log) |
| `python3 -B code/regenerate_certificate.py --output /private/tmp/cycle-classification-verification/regenerated_certificate.json` | 0 | 0.043 | [certificate-regeneration.log](certificate-regeneration.log) |
| `python3 -B code/verify_five.py --certificate /private/tmp/cycle-classification-verification/regenerated_certificate.json` | 0 | 0.123 | [regenerated-certificate-verification.log](regenerated-certificate-verification.log) |
| `tectonic --keep-logs --keep-intermediates --outdir /private/tmp/cycle-classification-verification/paper paper.tex` | 0 | 0.630 | [paper-build-1.log](paper-build-1.log) |
| `tectonic --keep-logs --keep-intermediates --outdir /private/tmp/cycle-classification-verification/paper paper.tex` | 0 | 0.562 | [paper-build-2.log](paper-build-2.log) |
| `pdftoppm -r 110 -png /Users/tynandaly/basin/experiments/q-theory/ty-1/paper.pdf /private/tmp/cycle-classification-verification/committed/page` | 0 | 2.139 | [render-committed.log](render-committed.log) |
| `pdftoppm -r 110 -png /private/tmp/cycle-classification-verification/paper/paper.pdf /private/tmp/cycle-classification-verification/rebuilt/page` | 0 | 2.173 | [render-rebuilt.log](render-rebuilt.log) |

Exact versions are in the version logs. `pdflatex` is documented as an
alternative, but was not the compiler used in this run. First-install cache
setup was not rerun; the pinned existing Lean/Mathlib environment was used.

## Citation and scope audit

The publisher PDFs were downloaded and all 13 cited page images inspected.
The 2024 Lemma 1 and Theorem 3 / Eq. (8) are on printed p. 217 (PDF page 13).
Theorem 7 / Eq. (25) and the unnumbered prefix factors are on printed p. 240
(PDF page 36). Conjecture 1 is on p. 241 (PDF page 37). The 2021 Theorem 5 /
Eq. (23) is on p. 298 (PDF page 24). URLs and file/image hashes are in
[citation_sources.json](citation_sources.json).

The recurrence range remains w>=1; the universal equivalence remains w>=2.
Positive-position classification is not generalized to vanishing non-head
rates. C5 head-only connectivity has its distinct stronger scope. Odd-cycle
examples at w=1 do not meet the conjecture's bipartite hypothesis. The
all-factor exclusion remains the explicit five-job certificate. Tested
canonical balance at theta=1 is identified as computational evidence on
the family n=2w+1. No convergence timescale is asserted.

The unavailable historical `cycle_checks.json`, `symmetric_checks.json`, and
`nine_job_checks.json` were not described as packaged or replayed. The new
`results/nine_job.json` is a fresh complete reproduction of the C9 check.
The arbitrary-size classification and residual theorems do not rely on
those finite experiments. The package preserves all available earlier
verification inputs and scripts.

## Package integrity

[PACKAGE.md](../PACKAGE.md) gives full replay and archive commands. The
archive contains every tracked file, plus `SOURCE_COMMIT.txt` and a complete
`SHA256SUMS`. The adjacent archive checksum covers the `.tar.gz` itself.
No email, release, push, or public-archive update was performed.
