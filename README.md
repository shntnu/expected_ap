# Average precision under random ranking

A short mathematical note by Shantanu Singh and Anne E. Carpenter.
The chance mean of AP exceeds prevalence whenever relevant and irrelevant items are both present.
This paper gives exact mean and variance formulas, explicit boundary cases, two asymptotic regimes, and accompanying Lean proofs under uniform random ranking with a fixed positive count.

The harmonic expectation and its derivation were obtained independently of Manzhos et al. and recorded on [September 7, 2025](https://github.com/shntnu/expected_ap/blob/4efbcf57d0d28a158dcbbe52872847d8e21ba130/expected_ap.md), before their [November 4, 2025 preprint](https://arxiv.org/abs/2511.02571). The Lean expectation proof followed in March 2026, and the second-moment derivation and variance verification in July 2026.
See [VERIFICATION.md](VERIFICATION.md#provenance) for the source commits.

[Read the paper (PDF)](https://github.com/shntnu/expected_ap/releases/download/v1.0.1/paper.pdf) | [Download the reproducible supplement](https://github.com/shntnu/expected_ap/releases/download/v1.0.1/supplement.zip) | [Version 1.0.1](https://github.com/shntnu/expected_ap/releases/tag/v1.0.1)

## Cite

Singh, S., and Carpenter, A. E. (2026).
*Average precision under random ranking: baseline, variability, and formal verification* (Version 1.0.1).
Broad Institute of MIT and Harvard.
[Versioned release](https://github.com/shntnu/expected_ap/releases/tag/v1.0.1).

Use GitHub's **Cite this repository** button or copy [CITATION.bib](CITATION.bib).
[CITATION.cff](CITATION.cff) provides the author and version metadata in a machine-readable format.

## Use the formulas

`moments.py` uses only the Python standard library and returns exact `fractions.Fraction` values.
Pass integer counts with L >= 1 and 0 <= M <= L; zero positives give mean and variance zero by the paper's convention.
Invalid count ranges raise `ValueError`, and noninteger inputs raise `TypeError`.
From the supplement root, with `uv` installed:

```bash
uv run --locked python - <<'PY'
from math import sqrt
from moments import expected_ap, var_ap

mean = expected_ap(8, 2)
variance = var_ap(8, 2)
print(mean)                         # 3403/7840
print(float(mean), sqrt(variance))  # Mean about 0.434056; SD about 0.208750
PY
```

These are the moments of full-list, noninterpolated AP under uniform random ranking with the positive count fixed.
Each calculation uses O(L) rational-arithmetic operations to sum harmonic numbers; the integer sizes grow with L, so this reference implementation is intended for exact checks and moderate list lengths.
`demo.enumerate_ap(L, M)` returns exact AP values and their counts over all binomial(L, M) label vectors, so exhaustive enumeration is practical only for small cases.

## Reproduce

The standalone `supplement.zip` and a Git checkout already contain the complete source tree.
When using the full arXiv source download, first extract `anc/supplement.zip` into the source root beside `main.tex`, preserving its paths.
Run the commands below from that source root.

For the Python checks and figure/table generation, only `uv` is needed:

```bash
uv run --locked python verify.py
uv run --locked python demo.py
```

These commands install the pinned Python environment and do not require TeX or Lean.
They generate the figure and two CSV tables under `build/`.

For the complete workflow, also install a TeX distribution with pdfLaTeX and the packages used in `main.tex`, and `elan` for Lean toolchains.
From the supplement root:

```bash
bash reproduce.sh
```

The first run installs Python dependencies from `uv.lock` and obtains the Lean toolchain and pinned Mathlib cache.
It needs network access and several GB of disk space.
Later runs can reuse those caches.
The script fails if any Python check, paper compilation, Lean build, or axiom audit fails.

Outputs are `build/main.pdf`, the figure and two CSV tables under `build/`, build logs, `VERIFICATION.md`, and the source archives `build/supplement.zip` and `build/arxiv-source.zip`.
The plotted data are deterministic and computed in exact rational arithmetic; rendering may vary with fonts and tool versions.
The checked-in `figures/ap.pdf` permits the paper to compile without running Python.

For the paper alone:

```bash
mkdir -p build
pdflatex -halt-on-error -output-directory=build main.tex
pdflatex -halt-on-error -output-directory=build main.tex
```

## Contents

- `main.tex`, `figures/ap.pdf`: complete paper source, including the mathematical appendices and references.
- `CITATION.cff`, `CITATION.bib`: citation metadata for the paper and supplement.
- `moments.py`: exact mean and variance reference implementation.
- `demo.py`: independent enumeration and figure/table generation.
- `verify.py`: published-variance equivalence and independent coefficient-sum checks.
- `lean/`: three proof modules, the theorem audit, and pinned build configuration.
- `verification_record.py`, `VERIFICATION.md`: validation and source fingerprints.
- `pyproject.toml`, `uv.lock`, `.python-version`: reproducible Python environment.
- `reproduce.sh`: the complete reproduction command.
- `package.py`: source-archive generation, also runnable from an extracted supplement without Git.

All 55 configurations with 1 <= M <= L <= 10 are checked by enumerating binary label vectors and independently scoring cumulative precision.
The 10 zero-positive cases with 1 <= L <= 10 and invalid count ranges are checked as well.
The four coefficient sums are checked directly for L = 1 through 15.
The variance matches the full-list specialization of Manzhos et al. symbolically.
These finite checks complement the general Lean proofs; they do not replace them.

The Lean audit checks the exact types and transitive axioms of eight named results.
The asymptotics and the interpretation of earlier literature are mathematical prose, not Lean-verified claims.

## Submission

The paper can be submitted as `main.tex` with `figures/ap.pdf`; references are embedded, so no BibTeX run or custom class is needed.
The upload package places the non-paper supplement files in `anc/supplement.zip`; the TeX source and figure remain at the source root.
The standalone `build/supplement.zip` also includes the paper source and figure.
The complete reproduction command regenerates both archives from the current sources after verification, including this README and the submission review.
Do not upload `.lake`, `.venv`, build logs, or the compiled manuscript PDF as part of the TeX source.
See [SUBMISSION_REVIEW.md](SUBMISSION_REVIEW.md) for recorded author details, acknowledgments, license and category choices, and remaining submission steps.
