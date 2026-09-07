# Submission review

Prepared for Shantanu Singh and Anne E. Carpenter on September 7, 2026.

The seven-page manuscript includes both mathematical appendices and five references.
The source archive contains `main.tex`, the vector figure, and the remaining reproducible supplement in `anc/supplement.zip`.
Extract the inner ZIP into the source root alongside `main.tex` before running the complete workflow.
The standalone `build/supplement.zip` contains the entire source tree in one archive.

## Reader review

The final review checked the paper and supplement from the following perspectives.

| Reader question | Where it is answered and what was checked |
| --- | --- |
| Which AP definition and random-ranking model apply? | Section 2 defines full-list, noninterpolated AP, fixed relevance counts, uniform rank subsets, rank direction, and individual ordering of ties. |
| Why is chance above prevalence, and by how much? | Proposition 1 derives the harmonic correction; Section 5 gives a concrete L = 8, M = 2 example with mean 0.434056 versus prevalence 0.25. |
| How variable is an individual AP score? | Proposition 2 gives exact variance; Section 5 reports SD 0.208750 for the example and describes the figure band as spread whose coverage depends on the discrete law. |
| When can the asymptotic variance be used? | Corollary 1 and Appendix B specify fixed prevalence and fixed positive count separately; Section 5 shows the finite-list discrepancy at L = 100, M = 10. |
| Are the derivations and boundary cases correct? | Both appendices were independently reviewed, both asymptotic leading terms were checked symbolically, and exact enumeration covers small lists including M = 0, M = 1, and M = L. |
| How does this relate to earlier work? | All four prior-work references and their mathematical descriptions were checked against primary sources; the published full-ranking variance is symbolically identical. |
| When was the independent expectation derivation recorded? | The introduction cites the September 7, 2025 manuscript and contrasts its date with the November 4, 2025 Manzhos et al. preprint; the March and July 2026 formalization stages are dated separately. |
| What exactly does Lean establish? | Section 6 and VERIFICATION.md identify theorem names, hypotheses, logical dependencies, and the scope of the formal proofs. |
| How can I calculate moments or reproduce the figure? | README.md provides a minimal Python example, separate Python-only commands, exact-arithmetic cost, enumeration cost, and the complete workflow. |
| Can the distributed files reproduce the paper? | The source archives contain explicit current inputs, locked dependencies, build instructions, the verification record, and their own packaging script. |

Primary sources used for the literature review were the [Zhang and Su author-uploaded paper](https://www.researchgate.net/publication/254043796_Statistical_inference_on_recall_precision_and_average_precision_under_random_selection), [Lopes and Bontempi publisher PDF](https://link.springer.com/content/pdf/10.1007/978-3-662-44851-9_21.pdf), [Bestgen publisher PDF](https://ufal.mff.cuni.cz/pbml/103/art-bestgen.pdf), and [Manzhos et al. published article](https://www.vmsta.org/journal/VMSTA/article/353/read). The review found no defect in the paper's mathematical results or citation mappings.
The changes clarify application and interpretation, align zero-positive Python behavior with the manuscript, correct two Lean source comments, and make archive generation part of reproduction.
The introduction and repository landing page also document the earlier independent expectation derivation with a citation to its original source.

## Completed checks

- Exact enumeration agrees with the mean and variance for all 65 cases with 1 <= L <= 10 and 0 <= M <= L, and invalid input checks pass.
- The four second-moment coefficient sums agree with direct enumeration for L = 1 through 15.
- Symbolic subtraction from the published full-ranking variance gives zero.
- All three Lean modules build, and eight audited results have only propext, Classical.choice, and Quot.sound as axiom dependencies.
- The complete reproduction command passes with locked Python dependencies and pinned Lean dependencies.
- The complete workflow also passes from the extracted arXiv source with a new Python environment and freshly built project proof modules.
  The regenerated figure, CSV tables, verification record, and both archives match the working-tree outputs byte for byte; extracted PDF text also matches.
- The PDF compiles without LaTeX warnings; all seven pages were visually inspected.

The Lean dependencies were reused from the pinned local cache; all nine package revisions match the manifest and have no tracked edits.
The three project modules were built from source in the extracted package.
The asymptotic arguments, Python code, and literature comparison are not certified by Lean.

## Recorded submission choices

- Authors, in order: Shantanu Singh and Anne E. Carpenter.
- Shared affiliation: Broad Institute of MIT and Harvard.
- Emails: shantanu@broadinstitute.org and anne@broadinstitute.org.
  The paper displays the shared-domain shorthand `{shantanu,anne}@broadinstitute.org`, with an individual email link for each author.
- Primary category: cs.IR (Information Retrieval); requested cross-list: math.PR (Probability).
- Intended license: CC0 1.0 for the paper and original supplementary material, following the preference for maximum permissiveness.
  CC0 permits reuse without an attribution condition; third-party dependencies retain their own licenses.
  This is the recorded submission choice, not a claim that either author has already completed final approval or that a public dedication has been submitted.
- Funding acknowledgment: We appreciate funding from the National Institutes of Health (NIH MIRA R35 GM122547 to AEC).
- The manuscript acknowledges Claude and Codex assistance in exploration, code, Lean proofs, literature comparison, and writing.

## Remaining before submission

- Both authors should approve the final manuscript, AI-assistance wording, author details, and CC0 choice.
- Check endorsement requirements in the submitting author's arXiv account.
- Inspect arXiv's generated PDF and metadata before final submission.

CC BY 4.0 is an alternative if the authors want permissive reuse with legally required attribution.
CC0 is the most permissive available option and does not impose that condition.
The license selected for a posted version is irrevocable.

This is a concise derivation and formal-verification note that recovers existing moment formulas.
Suitability and category placement remain subject to arXiv moderation.

Official submission references:

- [TeX submission](https://info.arxiv.org/help/submit_tex.html).
- [Ancillary files](https://info.arxiv.org/help/ancillary_files.html).
- [License options](https://info.arxiv.org/help/license/index.html).

The paper and supplement are prepared for the repository's `main` branch and versioned GitHub release `v1.0.1`.
The release includes the manuscript PDF, reproducible supplement, arXiv source package, and citation metadata.
No arXiv submission has been made.
