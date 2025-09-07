# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Repository Overview

This repository contains a mathematical analysis of Expected Average Precision (AP) under random ranking, implemented in both Python (for simulation/visualization) and Lean 4 (for formal proof).

## Commands

### Lean Development
- Build the Lean project: `cd lean && lake build`
- **Note**: The Lean proof is work in progress - contains incomplete proofs marked with `sorry` that need completion

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

2. **lean/expected_ap.lean**: Formal Lean 4 proof (work in progress) containing:
   - Definition of Average Precision for ranked lists
   - Harmonic number computation
   - Uniform averaging over permutations
   - Main theorem: `expected_ap_closed_form` proving E[AP] = (1/L) * ((M-1)/(L-1) * (L - H_L) + H_L)

3. **expected_ap.md**: Mathematical exposition of the theoretical results

## Key Mathematical Concepts

- **Average Precision (AP)**: Mean of precisions at ranks where positives occur
- **Expected AP under random ranking**: Prevalence + O(log L / L) bias term
- **Normalized AP (n*-AP)**: Scaled to [-1, 1] range for significance testing
- **Harmonic numbers**: H_L = Σ(1/k) for k=1 to L, appearing in the closed form

## Development Notes

- The Lean proofs use exchangeability arguments and hypergeometric distributions
- The Python simulation validates the closed-form expressions through Monte Carlo
- Both implementations handle edge cases (M=0, L=1) carefully
