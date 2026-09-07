#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p build
uv sync --locked
uv run --locked python verify.py | tee build/python-verification.log
uv run --locked python demo.py | tee build/demo.log
cp build/ap_baseline_variability.pdf figures/ap.pdf
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build main.tex > build/latex-pass1.log
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build main.tex > build/latex-pass2.log
(
    cd lean
    lake exe cache get
    lake build
    lake env lean verify.lean
) > build/lean.log 2>&1
uv run --locked python verification_record.py
printf 'Reproduced build/main.pdf, figure, tables, and verification record.\n'
