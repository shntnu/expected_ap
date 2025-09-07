# Expected Average Precision Under Random Ranking

Exact finite-sample analysis and computational methods for Expected Average Precision (AP).

## Overview

This repository contains the theoretical derivation and implementation showing that E[AP] under random ranking equals prevalence plus a O(log L/L) bias term, not just prevalence as commonly assumed.

See [`expected_ap.md`](expected_ap.md) for the full mathematical exposition, or [`expected_ap_simple.md`](expected_ap_simple.md) for a simplified step-by-step derivation.

## Quick Start

```bash
# Run the interactive notebook
marimo run expected_ap.py

# Or edit interactively
marimo edit expected_ap.py
```

## Repository Structure

- **`expected_ap.md`** - Complete mathematical paper with proofs
- **`expected_ap_simple.md`** - Simplified step-by-step derivation for accessibility
- **`expected_ap.py`** - Interactive marimo notebook demonstrating all results  [![Open in molab](https://molab.marimo.io/molab-shield.png)](https://molab.marimo.io/notebooks/nb_y1a7YRZf1h4JbRySEHfKSR)
- **`lean/`** - Formal proof in Lean 4 (work in progress)

## Key Result

Under uniformly random ranking with M relevant items out of L total:

**E[AP] = (1/L) × [(M-1)/(L-1) × (L - H_L) + H_L]**

where H_L is the L-th harmonic number. This corrects the naive approximation E[AP] ≈ M/L.
