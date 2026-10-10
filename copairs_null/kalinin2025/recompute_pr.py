"""Recompute mAP p-values from the paper's own AP tables with copairs#151's null and compare.

usage: recompute_pr.py IN_DIR OUT_DIR GROUP_COL NAME [NAME ...]
IN_DIR holds NAME_ap_scores.parquet and NAME_map_activity.csv written by the paper's pipeline (copairs 0.5.1)."""
import sys, warnings
from pathlib import Path
import numpy as np, pandas as pd
import importlib.metadata as md
from statsmodels.stats.multitest import multipletests
from copairs.map.map import get_map_pvalue

IN, OUT, GROUP = Path(sys.argv[1]), Path(sys.argv[2]), sys.argv[3]
OUT.mkdir(parents=True, exist_ok=True)
print("copairs", md.version("copairs"))
for name in sys.argv[4:]:
    ap = pd.read_parquet(IN / f"{name}_ap_scores.parquet")
    ap["normalized_average_precision"] = ap["average_precision"]  # feeds only a summary column, not the p-value
    old = pd.read_csv(IN / f"{name}_map_activity.csv")
    null_size = 100_000 if name in ("cp", "ne") else 1_000_000
    with warnings.catch_warnings(record=True) as w:
        warnings.simplefilter("always")
        new = get_map_pvalue(ap, [GROUP], null_size=null_size, seed=0, progress_bar=False)
    fallback = [x for x in w if "previous null" in str(x.message)]
    new = new[new[GROUP].astype(str) != "NA"].copy()
    _, new["corrected_p_value"], _, _ = multipletests(new["p_value"], method="fdr_bh")
    new["p < 0.05"] = new["corrected_p_value"] < 0.05
    m = old.merge(new[[GROUP, "mean_average_precision", "p_value", "corrected_p_value", "p < 0.05"]], on=GROUP, suffixes=("_v051", "_pr"))
    assert len(m) == len(old) and np.allclose(m["mAP"], m["mean_average_precision"]), "merge/mAP mismatch"
    m.to_csv(OUT / f"{name}_map_activity_compare.csv", index=False)
    n = len(m)
    up = int(((~m["p < 0.05_v051"]) & m["p < 0.05_pr"]).sum()); down = int((m["p < 0.05_v051"] & (~m["p < 0.05_pr"])).sum())
    print(f"{name}: {n} groups, null_size {null_size}, fallback warnings {len(fallback)}")
    print(f"   corrected p < 0.05: copairs 0.5.1 {int(m['p < 0.05_v051'].sum())} ({m['p < 0.05_v051'].mean():.1%}) | this PR {int(m['p < 0.05_pr'].sum())} ({m['p < 0.05_pr'].mean():.1%}) | gained {up}, lost {down}")
    print(f"   raw p < 0.05:       copairs 0.5.1 {int((m['p_value_v051'] < 0.05).sum())} | this PR {int((m['p_value_pr'] < 0.05).sum())}")
    band = m[(m["p_value_pr"] > 2 / (null_size + 1)) & (m["p_value_pr"] < 0.2)]
    print(f"   groups with PR p in (floor, 0.2): {len(band)}; median p ratio 0.5.1/PR there {(band['p_value_v051'] / band['p_value_pr']).median():.2f}")
