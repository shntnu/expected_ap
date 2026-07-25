# Average Precision Under Random Ranking: Exact Expectation and Distribution

Exact finite-sample analysis of the expectation and full distribution of Average Precision (AP).

## Overview

This repository provides closed finite formulas for the expectation and probability mass function of AP under random ranking.
The expected value is a harmonic-number expression, while the full law is the uniform pushforward of the `M`-subsets of the `L` ranks.

See [`ap_distribution.md`](ap_distribution.md) for the full mathematical exposition, or [`expected_ap_simple.md`](expected_ap_simple.md) for a simplified step-by-step derivation.

## Quick Start

```bash
# Run the interactive notebook
uvx marimo run --sandbox expected_ap.py

# Explore the exact AP distribution
uvx marimo run --sandbox ap_distribution.py

# Or edit interactively
uvx marimo edit --sandbox expected_ap.py
```

## Agent skill setup

The project-local `marimo-notebook` skill is recorded in `skills-lock.json` and installed into gitignored directories.
After cloning, run `npx skills@1.5.20 add marimo-team/skills -s marimo-notebook -a claude-code -a codex -y` from the repo root.
The lock records an observed hash but not agent targets or an immutable revision for this plain source; replay the command to update and inspect `git diff -- skills-lock.json` before committing an intentional upstream change.

## Repository Structure

- **`ap_distribution.md`** - Complete mathematical paper with proofs
- **`expected_ap_simple.md`** - Simplified step-by-step derivation for accessibility
- **`expected_ap.py`** - Interactive marimo notebook for the expected-value results  [![Open in molab](https://molab.marimo.io/molab-shield.png)](https://molab.marimo.io/notebooks/nb_y1a7YRZf1h4JbRySEHfKSR)
- **`ap_distribution.py`** - Interactive exact PMF and CDF explorer
- **`lean/expected_ap.lean`** - Formal proof of the expected value
- **`lean/ap_distribution.lean`** - Formal proof of the exact AP probability mass function
- **`ap_moments.py`** - Exact Var(AP), shared-positive covariance, design effect, and mAP null (tests in `test_ap_moments.py`, calibration study in `calibration_check.py`)
- **`AP_MOMENTS.md`** - Moments results with a per-claim PROVEN / VERIFIED / ASSUMED status table
- **`lean/ap_moments.lean`** - Formal proofs for the moments layer, including the general variance closed form

## Key Result

Under uniformly random ranking with M relevant items out of L total:

**E[AP] = (1/L) × [(M-1)/(L-1) × (L - H_L) + H_L]**

where H_L is the L-th harmonic number. This corrects the naive approximation E[AP] ≈ M/L.

If the relevant ranks are `1 <= R_1 < ... < R_M <= L`, then

**P(AP = a) = #{R : (1/M) sum_j j/R_j = a} / choose(L,M).**

The count is necessary because different rank sets can yield the same AP.
Exact tails can be computed recursively by conditioning on the final relevant rank.
For thresholds sufficiently close to either endpoint, the tail also has a one-line exact formula involving only a floor or ceiling and a binomial coefficient.
No general harmonic simplification is known: already for two relevant items, the tail reduces to a shifted divisor-summatory floor sum.

The variance also has a compact harmonic closed form, and APs within a mAP group are positively correlated through shared positives (design effect approaching 1.84 in replicate retrieval); see [`AP_MOMENTS.md`](AP_MOMENTS.md).

## Lean Formal Proof

The `lean/` directory contains complete Lean 4 + Mathlib formalizations of the expectation (`expected_ap_closed_form`), every atom of the distribution (`uniformAPMass_closed_form_explicit`), and the variance (`varianceAP_closed_form`), verified by `lake build` with no `sorry` placeholders.

The proof was developed collaboratively by Claude Opus 4.6 and GPT-5.4 (via Codex). The permutation counting infrastructure and harmonic identities were built by Claude; the downstream algebraic proofs and the identification of a necessary `M ≥ 1` guard on the theorem statement were contributed by GPT-5.4 in `lean/expected_ap_gpt_54.lean`.

## Generate PDFs

```bash
# Convert markdown papers to PDF
pandoc ap_distribution.md -o ap_distribution.pdf --pdf-engine=xelatex -V mainfont="TeX Gyre Termes" -V mathfont="TeX Gyre Termes Math"
pandoc expected_ap_simple.md -o expected_ap_simple.pdf --pdf-engine=xelatex -V mainfont="TeX Gyre Termes" -V mathfont="TeX Gyre Termes Math"
```
