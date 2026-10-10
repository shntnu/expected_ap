"""The paper's nELISA phenotypic-activity mAP (experiment 5, Figure 4A-B), saving the
AP-level table too so the mAP p-values can be recomputed under another null."""
import os, sys, time, warnings
from pathlib import Path
import pandas as pd
import importlib.metadata as md
from map_utils.map import calculate_map

OUT = Path(sys.argv[1]); OUT.mkdir(parents=True, exist_ok=True)
EXP = Path(os.environ.get("KALININ_MAP_REPO", "/home/user/carpenter-singh-lab/2025_kalinin_map")) / "experiments/5_nelisa"
print("copairs", md.version("copairs"))
cp_df = pd.read_parquet(EXP / "outputs/cellpainting_profiles_normalized.parquet")
ne_df = pd.read_parquet(EXP / "outputs/nelisa_profiles_normalized.parquet")
pair_config = {
    "pos_sameby": ["Metadata_broad_sample", "Metadata_control_index"], "pos_diffby": [],
    "neg_sameby": [], "neg_diffby": ["Metadata_broad_sample", "Metadata_control_index"],
}
map_config = {"null_size": 100000, "groupby_columns": ["Metadata_broad_sample"]}
ref_config = {"condition": "Metadata_control_type == 'negcon'", "reference_col": "Metadata_control_index"}
for name, df in (("cp", cp_df), ("ne", ne_df)):
    t0 = time.time()
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        map_scores, ap_scores = calculate_map(df, pair_config, map_config, reference_index_config=ref_config, return_ap_scores=True)
    map_scores = map_scores.query("Metadata_broad_sample != 'NA'")
    map_scores.to_csv(OUT / f"{name}_map_activity.csv", index=False)
    ap_scores.to_parquet(OUT / f"{name}_ap_scores.parquet", index=False)
    print(f"{name}: {len(map_scores)} compounds, {int(map_scores['p < 0.05'].sum())} with corrected p < 0.05 "
          f"({map_scores['p < 0.05'].mean():.3f}); AP rows {len(ap_scores)}; {time.time()-t0:.0f} s")
    print("   n_pos_pairs:", ap_scores["n_pos_pairs"].value_counts().to_dict(), "n_total_pairs:", ap_scores["n_total_pairs"].value_counts().to_dict())
