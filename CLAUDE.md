# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Repository Overview

This repository contains a mathematical analysis of Expected Average Precision (AP) under random ranking, implemented in both Python (for simulation/visualization) and Lean 4 (for formal proof).

## Commands

### Lean Development
- Build the Lean project: `cd lean && lake build`
- If `lake` is not on PATH (elan shims missing), use the toolchain directly: `cd lean && ~/.elan/toolchains/leanprover--lean4---v4.23.0-rc2/bin/lake build`
- Check `lean/lean-toolchain` for the expected Lean version
- **Note**: The Lean proof is complete — all theorems compile with zero `sorry` placeholders
- Lean LSP MCP tools (`lean_goal`, `lean_diagnostic_messages`, etc.) are available for interactive proof development

### Python Development
- Run the marimo notebook: `marimo run expected_ap.py`
- Edit the notebook interactively: `marimo edit expected_ap.py`
- Python dependencies are inline in the script (PEP 723 format)

## Architecture

### Core Components

1. **expected_ap.py**: Marimo notebook containing:
   - Closed-form calculation of expected AP using harmonic numbers
   - Monte Carlo simulation for validation
   - Normalized AP metrics
   - Interactive visualizations with Altair

2. **lean/expected_ap.lean**: Complete Lean 4 + Mathlib formal proof containing:
   - Definition of Average Precision for ranked lists
   - Harmonic number computation and identities
   - Permutation counting via `decomposeFin` decomposition
   - Main theorem: `expected_ap_closed_form` proving E[AP] = (1/L) * ((M-1)/(L-1) * (L - H_L) + H_L)

3. **lean/expected_ap_gpt_54.lean**: Alternative proof path developed by GPT-5.4 via Codex, providing the downstream algebraic proofs and the `hM` guard fix

4. **expected_ap.md**: Mathematical exposition of the theoretical results

## Key Mathematical Concepts

- **Average Precision (AP)**: Mean of precisions at ranks where positives occur
- **Expected AP under random ranking**: Prevalence + O(log L / L) bias term
- **Normalized AP (n*-AP)**: Scaled to [-1, 1] range for significance testing
- **Harmonic numbers**: H_L = Σ(1/k) for k=1 to L, appearing in the closed form

## Development Notes

- The Lean proof uses `Equiv.Perm.decomposeFin` decomposition and `Equiv.mulRight` swap bijections for permutation counting (not exchangeability)
- `expected_ap_closed_form` requires `hM : numRelevant y ≠ 0` — when M=0, AP is 0 by convention but the harmonic formula is nonzero for L > 1
- The Python simulation validates the closed-form expressions through Monte Carlo
- Pre-commit hooks are configured (`.pre-commit-config.yaml`): trailing whitespace, large files, ruff for Python
