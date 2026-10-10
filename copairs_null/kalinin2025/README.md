# Is the copied mAP null in the mAP paper's results?

Yes. [carpenter-singh-lab/2025_Kalinin_mAP](https://github.com/carpenter-singh-lab/2025_Kalinin_mAP) pins `copairs==0.5.1`, whose `mean_average_precision` builds a group's mAP null from one AP draw copied across members with equal pair counts (`null_dists[rev_ix[indices]].mean(axis=0)`, `map.py` line 77), and the simulation code in `map_utils/eval_metrics/mean_ap.py` carries its own copy of the same expression.
Every mAP p-value in the paper goes through one of the two.
Per-profile AP p-values (the Mitocheck and single-cell Perturb-seq analyses) are unaffected, because the fix changes only the group-level null.

The scripts here rerun the paper's own pipeline on three of its results and recompute the mAP p-values with the per-similarity null of [copairs#151](https://github.com/cytomining/copairs/pull/151), from the paper's own AP tables.
Nothing else changes: same profiles, same preprocessing, same AP scores, same null size, same seed, same FDR correction.

## Results

Numbers in each pair are copairs 0.5.1 (the paper) then copairs#151.

**Cell Health, Figure 3B** (100 CRISPR guides per cell line, 6 replicate wells, 192 cutting-control wells, `null_size` 1,000,000). The figure's "Retrieved" percentage is the share of guides with FDR-corrected p < 0.05:

| cell line | retrieved, paper | retrieved, #151 | guides gained | guides lost |
|---|---:|---:|---:|---:|
| A549 | 31% | 50% | 19 | 0 |
| ES2 | 45% | 76% | 31 | 0 |
| HCC44 | 70% | 81% | 11 | 0 |

**nELISA, Figure 4A-B** (300 compounds, 4 wells each for 286 of them and 8 for 14, 256 DMSO wells, `null_size` 100,000; corrected p < 0.05):

| profiles | retrieved, paper | retrieved, #151 | gained | lost |
|---|---:|---:|---:|---:|
| Cell Painting | 88.3% (265) | 88.7% (266) | 1 | 0 |
| nELISA | 40.3% (121) | 45.0% (135) | 14 | 0 |

Cell Painting is saturated either way; the nELISA profiles, where the paper's point is that fewer compounds are retrievable, gain 14 compounds, and the 8-well compounds move most (for example p = 0.044 → 0.003 at mAP 0.115).

**Simulations, Figure 2** (mAP recall against the paper's other metrics): see below.

## What the paper's pipeline needed to run

Three things in the repository as committed stop `pip install .` plus the scripts from running today; none of them changes a number once fixed.

- `copairs==0.5.1` imports against `duckdb.duckdb.DuckDBPyRelation`, which later duckdb releases dropped, and the paper's `pyproject.toml` does not pin duckdb. `pip install "duckdb==1.2.2"` after `pip install .` restores the import.
- `experiments/1_simulations/0_run_simulations.py` imports `assign_reference_index` from `map_utils.map`, where it no longer exists. The copairs function of that name writes a boolean condition back as the index, so every control would get index 1, the controls would form one positive clique, and some perturbations would lose their group (recall denominators of 82 to 99 instead of 100). `run_sim.py` supplies the version the committed results imply: each control gets its own row index. With it, the copied-null rerun reproduces the committed `fig2_results.csv` exactly at 2 and 3 replicates and within a few counts at 4.
- `map_utils/eval_metrics/mean_ap.py` calls `copairs.compute.get_distance_fn`, which existed only in copairs 0.4.2 to 0.4.4; `run_sim.py` maps it to today's `get_similarity_fn`.

## Run

Two environments, both Python 3.11 with the paper's pins:

```bash
# A: the paper as published
uv venv --python 3.11 venv_paper && VIRTUAL_ENV=venv_paper uv pip install /path/to/2025_Kalinin_mAP "duckdb==1.2.2"
# B: the same pins with copairs from copairs#151 (branch fix/joint-map-null) dropped in
uv venv --python 3.11 venv_pr && VIRTUAL_ENV=venv_pr uv pip install /path/to/2025_Kalinin_mAP "duckdb==1.2.2" && VIRTUAL_ENV=venv_pr uv pip install --no-deps /path/to/copairs
export KALININ_MAP_REPO=/path/to/2025_Kalinin_mAP
```

Real data (nELISA ships in the repository; Cell Health needs `experiments/2_cellhealth/0_download_data.sh` for the nine plates, then `1_preprocess_data.py`):

```bash
cd $KALININ_MAP_REPO/experiments/5_nelisa && venv_paper/bin/python 0_preprocess_profiles.py
venv_paper/bin/python run_nelisa.py out/nelisa                       # the paper's mAP, plus the AP tables
venv_pr/bin/python recompute_pr.py out/nelisa out/nelisa_pr Metadata_broad_sample cp ne
venv_paper/bin/python run_cellhealth.py out/cellhealth
venv_pr/bin/python recompute_pr.py out/cellhealth out/cellhealth_pr Metadata_pert_name A549 ES2 HCC44
```

Simulations (the mAP metric only; the other metrics' recall is taken from the committed `fig2_results.csv`), about 40 minutes each:

```bash
NULL=copied venv_paper/bin/python run_sim.py save_file=results/fig2_copied.csv
NULL=joint  venv_paper/bin/python run_sim.py save_file=results/fig2_joint.csv
venv_paper/bin/python compare_sim.py results
```

`NULL=joint` swaps `mean_ap.py`'s `get_p_value` for the per-similarity null (`joint_map_null` from `../copairs_joint_null.py`, the sampler copairs#151 adds as `compute.random_map`) and leaves everything else, including the seeded simulated data, as the paper's code.
