# Expected Average Precision Analysis

Mathematical analysis and implementation of Expected Average Precision (AP) under random ranking.

## Overview

This project provides both theoretical derivation and practical implementation of the expected value of Average Precision when items are ranked uniformly at random. The key result shows that E[AP] = prevalence + O(log L / L), where L is the total number of items.

## Components

- **map.py** - Interactive Python notebook with simulations and visualizations
- **expected_ap.lean** - Formal proof in Lean 4 (work in progress - several incomplete proofs)
- **expected_ap.md** - Mathematical exposition

## Quick Start

### Python Simulation
```bash
# Run interactive notebook
marimo run map.py

# Edit notebook
marimo edit map.py
```

### Lean Proof
```bash
# Build the Lean project
lake build
```

## Key Results

For L items with M relevant items:
- **Expected AP**: E[AP] = (1/L) � [(M-1)/(L-1) � (L - H_L) + H_L]
- **Asymptotic behavior**: E[AP] � M/L as L � 
- **Normalized AP**: Scales AP to [-1, 1] for significance testing

Where H_L = �(1/k) for k=1 to L is the L-th harmonic number.
