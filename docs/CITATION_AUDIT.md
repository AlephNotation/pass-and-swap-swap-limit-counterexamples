# Citation audit: published versions of record

The locations below were checked against the page images of the publisher PDFs,
not inferred from extracted text, a preprint, or an earlier manuscript version.
All page citations in `paper.tex` use **printed journal page numbers**. The PDF
column gives the **one-based page number** in the complete publisher PDF.

## Dorsman and Gardner (2024)

Jan-Pieter Dorsman and Kristen Gardner, *New directions in pass-and-swap queues*,
Queueing Systems **107**, 205-256 (2024).

DOI: https://doi.org/10.1007/s11134-024-09914-1

Publisher PDF: https://link.springer.com/content/pdf/10.1007/s11134-024-09914-1.pdf

| Item used in the revised manuscript | Printed page | PDF page | Verified location and use |
|---|---:|---:|---|
| Definition 1, OI conditions | 210 | 6 | Prefix-increment rates, permutation invariance, positive singleton rates; the following paragraph explicitly guarantees positive head rates. |
| Section 2.3, swapping graph and mechanism | 211-212 | 7-8 | Graph definition starts on 211; the first-later-compatible replacement rule is on 212. |
| Section 3.1, closed tandem | 215 | 11 | Fixed population; a departure immediately joins the other queue's tail. |
| Placement order and adherence | 216 | 12 | Three adherence constraints defining the placement order; these reduce to `c || reverse(d)` for distinct labels. |
| **Lemma 1** | **217** | **13** | Orientation/placement-order preservation under unlimited P&S. Earlier draft references to p. 216 for this numbered lemma were wrong. |
| **Theorem 3 and Eq. (8)** | **217** | **13** | Unlimited closed-tandem stationary law, under the stated irreducibility hypothesis. Lemma 1 and Theorem 3 genuinely occur on the same printed page. |
| Section 5, fixed swap-limit definition | 234 | 30 | Definition directly above Example 8: the w-th displaced job departs. The initiating completion is not one of the replacements. |
| Counterexample 2 | 239 | 35 | Earlier product-form failure with w=1 and a complete three-class graph, hence outside the required bipartite regime. |
| **Theorem 7 and Eq. (25)** | **240** | **36** | Short-placement-order result. Eq. (25) is the stationary law; the explicit prefix-product formulas for Phi and Lambda are in an **unnumbered display immediately below it**. |
| **Conjecture 1** | **241** | **37** | Transience of taller states on a (w+1)-partite graph. The following paragraph describes the intended product-form consequence. |
| Lemma 3 and its proof | 252-253 | 48-49 | Partiteness is used in the at-most-color sense: the reverse implication constructs at most w+1 independent vertex sets. Every cycle therefore meets the hypothesis when w>=2. |
| Appendix C.2, allocation caveat | 254 | 50 | Explicitly notes that OI assumptions ensure positive service only at the heads. The manuscript's Conjecture 1 corollary needs positive position rates for validity at nonexceptional lengths; exceptional closure gives failure without this extra assumption. |

The current manuscript cites the explicit definition of the swap limit, not
Example 8 as evidence that the implemented transitions are correct. It does not
claim that Theorem 7 is refuted.

## Comte and Dorsman (2021)

Celine Comte and Jan-Pieter Dorsman, *Pass-and-swap queues*, Queueing Systems
**98**, 275-331 (2021). The author's given name is typeset with its accent in the
manuscript bibliography.

DOI: https://doi.org/10.1007/s11134-021-09700-3

Publisher PDF: https://link.springer.com/content/pdf/10.1007/s11134-021-09700-3.pdf

| Item used in the revised manuscript | Printed page | PDF page | Verified location and use |
|---|---:|---:|---|
| Section 3.1, definition | 284-285 | 10-11 | The formal minimum-index replacement recursion and resulting queue appear on p. 285. |
| Introduction, machine-cluster applications | 277-278 | 3-4 | Motivation for P&S models through scheduling and load distribution subject to machine-job compatibility constraints. |
| **Theorem 5 and Eq. (23)** | **298** | **24** | Original unlimited two-queue tandem product form; the normalizer is Eq. (24) on that page. |

**Equation numbers are paper-specific.** Eq. (25) on p. 298 of the 2021 paper is
a decomposition of the state space, not the stationary formula. References in
our paper to the canonical law in Eq. (25) explicitly mean the 2024 paper.

## What was changed or clarified

- Retained the correct p. 217 citations for both Lemma 1 and Theorem 3 (2024).
- Removed the stale p. 216 citation to Lemma 1 from the earlier consolidated note.
- Distinguished the unlimited law, Theorem 3 / Eq. (8), from the short-order law,
  Theorem 7 / Eq. (25).
- Described the prefix-product weights as the unnumbered display following
  Eq. (25), rather than assigning Eq. (25) to that display itself.
- Added printed and one-based PDF page numbers for both source papers.
- Preserved the irreducibility hypothesis when applying the unlimited theorem;
  the revised paper proves the needed within-orientation communication first.

## Consolidation recheck (7 September 2026)

Both complete publisher PDFs were downloaded again from the publisher URLs
above and the cited page images inspected. The archived page-location table
was confirmed, including printed 217 / PDF 13 for both the 2024 Lemma 1 and
Theorem 3, printed 240 / PDF 36 for Theorem 7 and Eq. (25), and printed 298 /
PDF 24 for the 2021 Theorem 5 and Eq. (23). Their SHA-256 values and local
inspection commands are recorded in the package's
`verification/evidence/citation_sources.json`.
The PDFs are external literature, not editable manuscript dependencies.

Theorem 7 also has a `(w+1)`-partite hypothesis. The manuscript's unrestricted
short-fiber proof uses the unlimited theorem after proving communication;
Lean proves this balance identity independently. Conjecture 1 retains that
partiteness hypothesis. For w=1 it requires bipartiteness, so odd-cycle
examples do not refute it. The public archive has not been updated.

The follow-up corollary in `paper.tex` fixes one job per cycle vertex and
separates the directions: exceptional lengths fail for every admissible OI
allocation; nonexceptional lengths are proved valid under positive position
rates. It does not claim general validity with zero non-head rates. The
motivating paragraph uses the 2021 introduction's machine-cluster
applications; the product-form explanation concerns the manuscript's
classwise normalized law.
