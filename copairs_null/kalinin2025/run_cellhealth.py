"""The paper's Cell Health phenotypic-activity mAP (experiment 2, Figure 3B), exactly as
4_phenotypic_activity.py::process_phenotypic_activity computes it, saving the AP tables too."""
import os, sys, time, warnings
from pathlib import Path
import importlib.metadata as md
import numpy as np, pandas as pd

EXP = Path(os.environ.get("KALININ_MAP_REPO", "/home/user/carpenter-singh-lab/2025_kalinin_map")) / "experiments/2_cellhealth"
sys.path.insert(0, str(EXP))
from map_utils.map import calculate_map
from cell_health_utils import subset_6_replicates

OUT = Path(sys.argv[1]); OUT.mkdir(parents=True, exist_ok=True)
print("copairs", md.version("copairs"))
profiles = pd.read_csv(EXP / "outputs/cell_health_profiles_merged_wholeplate_normalized_featureselected.tsv.gz", sep="\t")
print("profiles", profiles.shape)
pair_config = {
    "pos_sameby": ["Metadata_pert_name", "Metadata_control_index"], "pos_diffby": [],
    "neg_sameby": [], "neg_diffby": ["Metadata_pert_name", "Metadata_control_index", "Metadata_is_control"],
}
map_config = {"null_size": 1_000_000, "groupby_columns": ["Metadata_pert_name"]}
for cell in ["A549", "ES2", "HCC44"]:
    t0 = time.time()
    df6 = subset_6_replicates(profiles, cell)
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        map_scores, ap_scores = calculate_map(df6, pair_config, map_config, return_ap_scores=True)
    map_scores.to_csv(OUT / f"{cell}_map_activity.csv", index=False)
    ap_scores.to_parquet(OUT / f"{cell}_ap_scores.parquet", index=False)
    print(f"{cell}: {len(map_scores)} guides, {int((map_scores['p_value'] < 0.05).sum())} with raw p < 0.05, "
          f"{int(map_scores['p < 0.05'].sum())} with corrected p < 0.05; AP rows {len(ap_scores)}; {time.time()-t0:.0f} s")
    print("   n_pos_pairs:", ap_scores["n_pos_pairs"].value_counts().to_dict(), "| n_total_pairs:", ap_scores["n_total_pairs"].value_counts().to_dict())
