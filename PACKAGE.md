# Consolidated verification package

The package contains the revised PDF and self-contained editable LaTeX,
all project Lean sources, all Python verifiers and regeneration scripts,
exact certificates, graph inputs, expected results, theorem map, citation
audit, unsent email, and verification records. No release is published by
these commands. The earlier public archive is unchanged.

## Verify the supplied archive

Extract the `.tar.gz`, enter `cycle-classification`, and run:

```sh
shasum -a 256 -c SHA256SUMS
```

`SOURCE_COMMIT.txt` identifies the packaged Git revision. `SHA256SUMS`
covers every regular file except itself, including the source commit and
verification logs. The neighboring `.tar.gz.sha256` checks the archive file.
The verification report identifies the exact source commit tested; the
following records-only commit adds its outcomes. `input_sha256.json`
identifies all checked manuscript, proof, data, and documentation inputs.

## Environment

- Python 3.10+, standard library only for the numerical suite and packaging.
- Lean from `lean-toolchain`; Mathlib and all transitive packages are pinned
  by `lakefile.toml` and `lake-manifest.json`. Install Lean using elan, then
  run `lake exe cache get` on first setup. These third-party toolchain
  dependencies require a first download; `.lake` caches are not packaged.
- Tectonic plus Poppler (`pdftoppm`, `pdftotext`, `pdfinfo`) for the complete
  automated artifact replay. A normal LaTeX installation can also compile
  `paper.tex` twice with `pdflatex`, but that alternative is not the recorded
  Tectonic command. TeX packages are named in the preamble. There are no
  external image, bibliography, or private manuscript source dependencies.

Exact tool versions used for the recorded run are in `verification/*version.log`.

## Full automated replay

```sh
python3 code/verify_release.py --output-dir /tmp/cycle-verification-replay
```

This runs the full Lean build, all four axiom audits, full-root kernel
replay, the complete Python suite normally and with optimization, the Lean
certificate export consistency check, exact stationary-certificate
regeneration and independent verification, and two complete PDF builds.
It rejects unexpected axiom dependencies, stale expected results, differing
certificate data, TeX warnings, unresolved references, changes to inputs
during the run, or a page-render mismatch between supplied and rebuilt PDFs.
It records each actual command, exit status, elapsed time, and log; it stops
on failure. It does not infer success for unrun commands.

The program checks rendered-page equivalence at 110 dpi. Visual inspection
of the supplied page images is separately recorded in
`verification/visual_review.json`. Mathematical claim review and the exact
scope of computed results are documented in `LEAN.md` and the report. The
program does not claim to automate those reviews.

For the numerical suite alone:

```sh
python3 run_checks.py
python3 -O run_checks.py
```

Each component can be invoked directly:

```sh
python3 code/verify_five.py --certificate data/stationary_certificate.json
python3 code/verify_orbits.py
python3 code/verify_uniform.py
python3 code/verify_classification.py
python3 code/verify_nine.py
python3 code/verify_screen.py
```

`verify_screen.py` regenerates the complete bipartite graph list and checks
coverage. `verify_nine.py` enumerates the entire C9 exceptional class and
checks both generators with integer flows. The complete suite compares
fresh JSON objects with all six committed `results/*.json` files.

## Stationary certificate

```sh
python3 code/regenerate_certificate.py --output /tmp/regenerated_certificate.json
python3 code/verify_five.py --certificate /tmp/regenerated_certificate.json
python3 -B code/export_lean_certificate.py --check
```

The generator solves a rational 45-orbit system and expands to 180 states.
The separate verifier reconstructs the full generator, checks all exact
balance equations and the nonzero factorization determinant, and does not
trust the stationary solver. The full replay also compares regenerated and
committed certificate JSON for exact equality.

## Build a new local package

From a Git checkout after committing the intended files:

```sh
python3 code/build_package.py --output /tmp/cycle-classification-verification.tar.gz
```

The script packages `git archive HEAD`, so unrelated local changes and
untracked files are not included. All tracked local sources are retained.
It adds complete file hashes and the exact revision. It does not push,
send the covering email, create a release, or update an archive service.

The downloaded publisher PDFs are external references, not manuscript
dependencies. Their URLs, page locations, checksums, and inspection method
are in `docs/CITATION_AUDIT.md` and `verification/citation_sources.json`.
