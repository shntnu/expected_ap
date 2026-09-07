# Average precision under random ranking

A short mathematical note by Shantanu Singh and Anne E. Carpenter.
This branch contains only the manuscript and its reproducible supplement.
The exploratory work remains in the repository's earlier history and `main` branch.

## Reproduce

Install `uv`, a TeX distribution with pdfLaTeX and the standard packages used in `main.tex`, and `elan` for Lean toolchains.
From the repository root:

```bash
bash reproduce.sh
```

The first run installs Python dependencies from `uv.lock` and obtains the Lean toolchain and pinned Mathlib cache.
It needs network access and several GB of disk space.
Later runs can reuse those caches.
The script fails if any Python check, paper compilation, Lean build, or axiom audit fails.

Outputs are `build/main.pdf`, the figure and two CSV tables under `build/`, build logs, and `VERIFICATION.md`.
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
- `moments.py`: exact mean and variance, extracted from the original implementation.
- `demo.py`: independent enumeration and figure/table generation.
- `verify.py`: published-variance equivalence and independent coefficient-sum checks.
- `lean/`: three proof modules, the theorem audit, and pinned build configuration.
- `verification_record.py`, `VERIFICATION.md`: validation and source fingerprints.
- `pyproject.toml`, `uv.lock`, `.python-version`: reproducible Python environment.
- `reproduce.sh`: the complete reproduction command.

All 55 configurations with 1 <= M <= L <= 10 are checked by enumerating binary label vectors and independently scoring cumulative precision.
The four coefficient sums are checked directly for L = 1 through 15.
The variance matches the full-list specialization of Manzhos et al. symbolically.
These finite checks complement the general Lean proofs; they do not replace them.

The Lean audit checks the exact types and transitive axioms of eight named results.
The asymptotics and the interpretation of earlier literature are mathematical prose, not Lean-verified claims.

## Submission

The paper can be submitted as `main.tex` with `figures/ap.pdf`; references are embedded, so no BibTeX run or custom class is needed.
The upload package places this reproducible supplement under arXiv's `anc/` directory.
Do not upload `.lake`, `.venv`, build logs, or the compiled manuscript PDF as part of the TeX source.
See the separate review checklist delivered with the prepared archive for author and submission decisions.
