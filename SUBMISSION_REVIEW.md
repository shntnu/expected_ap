# Submission review

Prepared for Shantanu Singh and Anne E. Carpenter on September 7, 2026.

The seven-page manuscript includes both mathematical appendices and four references.
The source archive contains main.tex, the vector figure, and the complete reproducible supplement in anc/supplement.zip.

## Completed checks

- Exact enumeration agrees with the mean and variance for all 55 cases with 1 <= M <= L <= 10.
- The four second-moment coefficient sums agree with direct enumeration for L = 1 through 15.
- Symbolic subtraction from the published full-ranking variance gives zero.
- All three Lean modules build, and eight audited results have only propext, Classical.choice, and Quot.sound as axiom dependencies.
- The complete reproduction command passes with locked Python dependencies and pinned Lean dependencies.
- The PDF compiles without LaTeX warnings; all seven pages were visually inspected.

The Lean dependencies were reused from the pinned local cache; the three project modules were built in this new checkout.
The asymptotic arguments, Python code, and literature comparison are not certified by Lean.
The development dates are repository evidence of independent work, not proof of global discovery priority or public availability.

## Recorded submission choices

- Authors, in order: Shantanu Singh and Anne E. Carpenter.
- Shared affiliation: Broad Institute of MIT and Harvard.
- Emails: shantanu@broadinstitute.org and anne@broadinstitute.org.
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

The submission branch is prepared for GitHub review.
No arXiv submission has been made.
