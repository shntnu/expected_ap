Three things stop a fresh `pip install .` and the scripts from running as committed. None of them changes a result; with all three in place, the unmodified `0_run_simulations.py` reproduces the mAP column of `results/fig2_results.csv` at 100 features (55 of 63 cells identical, the rest within 0.05, which is the run-to-run jitter of 100 simulated perturbations).

- **duckdb pin.** `copairs==0.5.1` imports `duckdb.duckdb.DuckDBPyRelation`, which later duckdb releases dropped, so `import copairs` fails in a fresh environment. `pyproject.toml` pins every other dependency exactly; this adds `duckdb==1.2.2` (the current release when copairs 0.5.1 was published).
- **`assign_reference_index` in the simulations.** `0_run_simulations.py` imports it from `map_utils.map`, where v0.2.0 removed it in favour of `copairs.matching.assign_reference_index`. The copairs function writes its `condition` argument back as the index, so the boolean Series the script passes would give every control index 1, the controls would form one positive clique, and some perturbations would lose their group (recall denominators of 82 to 99 instead of 100). The script now imports the copairs function and passes the row Index of the controls, which is what the original `map_utils` helper assigned (`df.loc[condition].index`).
- **`get_distance_fn` in `mean_ap.py`.** That helper existed in copairs 0.4.2 to 0.4.4; in 0.5.x the batched similarity function is `get_similarity_fn`, with the same `(feats, pair_ix, batch_size)` call.

Checked in a fresh Python 3.11 environment from the patched `pyproject.toml`: `import copairs` and `map_utils` succeed; `0_run_simulations.py` runs unmodified with all four metrics (reduced size) and, with the mAP metric at the paper's settings, matches the committed `fig2_results.csv` at 100 features as above.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01SdLgTRrN1KcuZ8YhfmVvA3
