# Joint mAP null for copairs

These are the checks behind [cytomining/copairs#151](https://github.com/cytomining/copairs/pull/151), which fixes the null distribution copairs uses for mAP p-values.
copairs currently draws one AP null per distinct `(n_pos_pairs, n_total_pairs)` configuration and averages the rows a group's members point at.
Members with equal counts point at the same row, so a group's mAP null is a single AP null copied across its members and never narrows as replicates are added.
The proposed null draws one random number per pair instead: a positive pair inside the group enters both members' rank lists, each member's AP comes from its own sorted list, and the group's mAP is their mean.

This folder is not part of the paper or its supplement; `package.py` and `verification_record.py` do not read it.

## Run

```bash
cd copairs_null
uv run copairs_joint_null.py --quick   # moments, distributions, graph oracle, atom, singleton
uv run copairs_joint_null.py           # adds the four-wells fixture, false-positive rates, and timing
```

The singleton check also compares against `copairs.compute.random_ap` when copairs is importable, either from a checkout beside this repository (`../copairs/src` relative to the repository root) or through `PYTHONPATH`.
The four-wells check reads `copairs_null_evidence.json`, which is not committed here; without it that check prints `SKIP`.

## What the checks establish

- Each member's mean and variance match `expected_ap` and `var_ap`, which are proven in `../lean/`.
- Pairwise covariance and `sd(mAP)` match `cov_ap`, `cov_ap_hetero` and `map_null_sd`, which are exact under the shared-pair model but are not Lean-proven.
- The whole mAP distribution matches a brute-force simulator that draws every similarity explicitly, for replicate groups and for two non-complete pair graphs.
- P(both APs = 1) for two members and four controls equals 1/9.
- A one-member group reproduces the exact AP law and copairs' `random_ap`.
- Over 30,000 true-null experiments per row, the false-positive rate holds the nominal 0.05 and 0.01 levels when similarities are exchangeable noise. With cosine similarity on 50 independent features it runs slightly high, most at 20 replicates (0.062 and 0.017).

## Files

- `copairs_joint_null.py`: the joint sampler and every check above.
- `map_null_effect.py`: what the copied null costs. The p-value copairs reports for a group whose true p-value is 0.05, 0.01 or 0.001, and the share of real hits each null detects, by group size.
- `figure_data.py`, `figure_data.json`: everything the figures and the explainer page plot, in one file (about ten minutes to regenerate).
- `figures.py`, `figures/`: the three PNG figures for copairs#151, drawn from `figure_data.json`.
- `ap_moments.py`, `calibration_check.py`: closed-form moments and null-data simulators, as of commit `a963209`.
- `copairs_joint_null.patch`: the full diff of copairs#151 (`d5bed2b`) against copairs `main` at `e16a40d`.
