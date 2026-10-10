"""Run the paper's Figure 2 simulation for the mAP metric only.

Fixes the stale import in 0_run_simulations.py (assign_reference_index lives in
copairs.matching) and, with NULL=joint, swaps the paper's copied null for the
per-similarity null of copairs#151 (joint_map_null from expected_ap/copairs_null).
Everything else, including the simulated data (seeded), is the paper's own code.
"""
import os, sys, functools
from pathlib import Path
import numpy as np
import map_utils.map as mm
import pandas as pd
def assign_reference_index(df, condition, reference_col="Metadata_Reference_Index", default_value=-1):
    """Give each control its own index (its row label); everything else gets default_value.

    0_run_simulations.py imports this from map_utils.map, where it no longer exists. copairs'
    version writes a boolean condition back as the index, so every control would get index 1
    and all controls would form one positive clique; the paper's committed results (recall
    denominators of exactly 100) show the controls were indexed individually."""
    df = df.copy()
    df[reference_col] = default_value
    if isinstance(condition, str):
        idx = df.query(condition).index
    elif isinstance(condition, pd.Series) and condition.dtype == bool:
        idx = df.index[condition.values]
    else:
        idx = condition
    df.loc[idx, reference_col] = idx
    return df
mm.assign_reference_index = assign_reference_index

import map_utils.eval_metrics.mean_ap  # noqa: F401
mean_ap_mod = sys.modules["map_utils.eval_metrics.mean_ap"]  # the package re-exports mean_ap as a function
from copairs import compute as _compute
if not hasattr(_compute, "get_distance_fn"):
    # the paper's mean_ap.py was written against copairs 0.4.x; the batched similarity helper is now get_similarity_fn
    import inspect as _inspect
    _kw = {"progress_bar": False} if "progress_bar" in _inspect.signature(_compute.get_similarity_fn).parameters else {}
    _compute.get_distance_fn = lambda distance: _compute.get_similarity_fn(distance, **_kw)
MODE = os.environ.get("NULL", "copied")
if MODE == "joint":
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))  # expected_ap/copairs_null
    from copairs_joint_null import joint_map_null, replicate_group

    @functools.lru_cache(maxsize=None)
    def joint_null(negatives, null_size, seed):
        members, edges = replicate_group(len(negatives), list(negatives))
        return joint_map_null(members, edges, null_size, seed)

    def get_p_value(map_score, indices, null_dists, null_size, rev_ix, _confs=None):
        confs = get_p_value.confs[rev_ix[list(indices)]]  # (num_pos, total) per member
        negatives = tuple(int(t - m) for m, t in confs)
        null = joint_null(negatives, null_size, get_p_value.seed)
        return (int((null > map_score).sum()) + 1) / (null_size + 1)

    # mean_ap() computes null_confs_unique locally; capture it by wrapping get_null_dists
    _orig_get_null_dists = mean_ap_mod.compute.get_null_dists
    def capture(null_confs_unique, null_size, seed):
        get_p_value.confs = np.asarray(null_confs_unique)
        get_p_value.seed = seed
        return _orig_get_null_dists(null_confs_unique, null_size, seed=seed)
    mean_ap_mod.compute.get_null_dists = capture
    mean_ap_mod.get_p_value = get_p_value
    print("NULL=joint: mAP p-values use the per-similarity null (copairs#151)")
else:
    print("NULL=copied: mAP p-values use the paper's null (one draw copied across members)")

sys.argv = [sys.argv[0]] + sys.argv[1:] + ["~metrics_config.mp_value", "~metrics_config.mmd", "~metrics_config.kmeans"]
SIM = os.path.join(os.environ.get("KALININ_MAP_REPO", "/home/user/carpenter-singh-lab/2025_kalinin_map"), "experiments/1_simulations")
os.chdir(SIM)
import runpy
runpy.run_path(os.path.join(SIM, "0_run_simulations.py"), run_name="__main__")
