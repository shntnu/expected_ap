# AP moments: variance, covariance, and the mAP null

`expected_ap.lean` proves the mean of Average Precision under a uniformly random ranking.
This branch adds the second moment, the covariance between two APs that share a positive, and the exact null law of mAP.
The point is a usable null for mAP, so the covariance matters: profiles that share relevant items are not independent, and treating them as independent understates the spread of mAP by roughly a factor of 1.84 in variance.

Files: `ap_moments.py` (the formulas), `test_ap_moments.py` (checks against exhaustive enumeration), `calibration_check.py` (does the correction fix the false-positive rate), `lean/ap_moments.lean` (the formalisation, one `sorry`).

## The one model

A profile ranks `L` items, `M` of them relevant, with `1 <= M <= L`.
Under the null the ranking is uniform, so the set of ranks holding the relevant items is uniform over the `C(L, M)` size-`M` subsets, and for sorted relevant ranks `R_1 < ... < R_M`

```
AP = (1/M) * sum_{j=1}^{M} j / R_j.
```

Everything below is a statement about that law.
`H_L = sum_{k<=L} 1/k` and `H2_L = sum_{k<=L} 1/k^2` throughout.

## Tier 1: the marginal law of one AP

Mean:

```
E[AP] = (1/L) * ( (M-1)/(L-1) * (L - H_L) + H_L )
```

Variance, via `W = M * AP = sum_{1<=i<=k<=L} Z_i Z_k / k` where `Z_k` indicates that rank `k` is relevant, and `m_r = C(M,r)/C(L,r)` (the probability that `r` prescribed ranks are all relevant, zero for `r > M`):

```
E[W]   = m1*H + m2*(L - H)
E[W^2] = m1*H2
       + m2*(2H^2 + 3H - 5H2)
       + m3*(2LH + 5L - 5H^2 - 9H + 7H2)
       + m4*(L^2 - 2LH - 5L + 3H^2 + 6H - 3H2)

Var(AP) = (E[W^2] - E[W]^2) / M^2
```

`W^2` expands into a sum over index pairs whose expectation depends only on how many distinct ranks are involved, which is why exactly `m1` through `m4` appear.
Edge cases: `Var = 0` at `M = L`, and `Var = H2_L/L - (H_L/L)^2` at `M = 1`.

## Tier 2: two APs that share a positive

This tier is a statement about a **model**, not about the ranking law alone.
Profiles `i` and `j` each rank `L` items with `M` relevant.
Exactly one relevant item is shared, and it is the pair `(i, j)` itself, carrying literally the same similarity value in both lists.
Every other value in both lists is an independent draw from the same continuous distribution.
That is the standard replicate-retrieval setup, but it is an assumption about the data.

Conditioning on the shared value's quantile `p` makes the two lists independent, so `Cov = Var_{p ~ U(0,1)}( E[AP | p] )`.
With the shared item at rank `u`, the other `M-1` positives are a uniform `(M-1)`-subset of the remaining `L-1` ranks, giving `E[AP | U=u] = (a + b/u + c*H_u)/M` with

```
q  = (M-1)/(L-1)
q2 = (M-1)(M-2)/((L-1)(L-2))          (0 if M < 3 or L < 3)
b  = 1 - 2q + q2
c  = q2 - q  = -(M-1)(L-M)/((L-1)(L-2))
A  = (b+c)/L = (L-M)(L-2M)/(L(L-1)(L-2))
a  = 2q*H_L + q + q2*(L-1-2H_L)
```

Mixing over `p` (rank `= 1 + Binomial(L-1, 1-p)`) turns this into `(a + A*g(p) + c*(H_{L-1} - l(p)))/M` with `g(p) = sum_{k<L} p^k` and `l(p) = sum_{k<L} p^k/k`.
The constant `a` drops out and the three remaining moments each collapse to one harmonic sum:

```
Var(g)    = 1 + 2L(H_{2L-1} - H_L) - H_L^2
Cov(g,l)  = sum_{j=1}^{L-1} (1/j)(H_{L+j} - H_j) - ((L-1)/L) * H_L
Var(l)    = sum_{j=1}^{L-1} (1/(j(j+1)))(H_{L-1} + H_{j+1} - H_{L+j}) - ((L-1)/L)^2

Cov(AP_i, AP_j) = ( A^2*Var(g) - 2*A*c*Cov(g,l) + c^2*Var(l) ) / M^2
```

`O(L)` work, and nonnegative by construction because it is the variance of a linear combination.

The consequence for mAP over `n` exchangeable profiles that pairwise share one positive is the design effect

```
DE = Var(mAP) / (Var(AP)/n) = 1 + (n-1) * Cov/Var
```

For fixed `M` and `L -> infinity`, `Cov/Var -> (12 ln 2 / pi^2)/M = 0.8428/M`.
In replicate retrieval, where `n` replicates give `M = n-1` positives each, the design effect therefore tends to `1 + 12 ln 2 / pi^2 = 1.8428` for **every** `n`.
That limit is why the whole replicate family clusters near 1.84 at realistic list lengths.
It is not universal: on short lists with many replicates it decays, to 1.40 at `L = 20, n = 12`.

## Tier 3: the exact mAP null under independence

`exact_map_pmf` gives the exact finite law of `mAP = (1/n) sum_i AP_i` for **independent** `AP_i`, in exact rational arithmetic with no floating point.
Each per-profile law is put on the integer grid `K / (M * lcm(1..L))` by a rank-inclusion dynamic program that never enumerates the `C(L, M)` subsets, all profiles are rescaled to a common grid, and the laws are convolved as integer polynomials.
`exact_map_tail` sums the upper tail of that law.

Independence is the assumption, and tier 2 says it is false whenever profiles share positives.
So tier 3 is the right null only when the profiles genuinely do not share relevant items.
It is also the reference the moment formulas are checked against.

## Status of every claim

| Claim | Status | Evidence |
| --- | --- | --- |
| `E[AP]` closed form | **PROVEN in Lean** | `expected_ap_closed_form`, `lean/expected_ap.lean`, no `sorry` |
| `E[AP] = E[W]/M` in the `m_r` language | **PROVEN in Lean** | `uniformAvgAP_eq_expectedW_div`, `lean/ap_moments.lean` |
| AP law = uniform law on `M`-subsets | **PROVEN in Lean** | `lean/ap_distribution.lean`; extended to arbitrary rank-set statistics by `uniformAvgOverPerms_comp_relevantRanks` |
| `Var(AP) >= 0`; `Var = 0` at `M = 0` and `M = L`; `Var = H2/L - (H/L)^2` at `M = 1` | **PROVEN in Lean** | `varianceAP_nonneg`, `varianceAP_closed_form_of_numRelevant_eq_{zero,one,card}` |
| **General `Var(AP)` closed form** | **NOT PROVEN. VERIFIED numerically** | `varianceAP_closed_form` in `lean/ap_moments.lean` is the file's single `sorry`. Verified by exhaustive enumeration of every rank subset for all `1 <= M <= L <= 12` (`test_ap_moments.py`), and inside Lean by `native_decide` on exact rationals for twelve `(L, M)` up to `L = 10`. |
| `Cov(AP_i, AP_j)` for a shared positive | **ASSUMED model, then exact** | Nothing in Lean covers it. Given the model it is exact, checked against exact rational integration over the shared quantile for all `1 <= M <= L` with `2 <= L <= 7`, and against direct simulation of the model. |
| `design_effect`, the correction inside `map_null_sd` | **ASSUMED (inherits tier 2)** | Exact ratio of two tier-2 quantities |
| `Cov(AP_i, AP_j)` for **mismatched** `(L, M)` pairs | **ASSUMED model, then exact** | `cov_ap_hetero`: the same conditioning argument with per-list coefficients; the two cross terms `Cov(g1,l2)` and `Cov(l1,g2)` no longer merge. Checked against exact rational integration of the model for all `L1, L2 <= 5`, reduces exactly to `cov_ap` on the diagonal for `L <= 12`, and two independent derivations agreed exactly on all 6084 configs with `L1, L2 <= 12`. Replaces the former `sqrt(cov_i * cov_j)` guess in `map_null_sd`. |
| `exact_map_pmf` / `exact_map_tail` | **VERIFIED, assumes independence** | Matches brute-force enumeration for single profiles; mass sums to exactly 1; its mean and variance match `expected_map` and `sum var_ap / n^2` exactly |

The `sorry` is isolated in `section Unproved` at the end of `lean/ap_moments.lean`, and `lake build` reports it as its only warning.
Nothing else in the file depends on it.
The `native_decide` checks are stated as anonymous `example`s, so no named theorem carries `Lean.ofReduceBool`.

An independent re-derivation done for this review recomputed AP from label vectors the way a retrieval library does (sort by score, cumulative true positives over rank, averaged over the positives) rather than through `(1/M) sum j/R_j`, and reproduced both `expected_ap` and `var_ap` exactly for all 78 configurations with `L <= 12`.

## Calibration: does the correction actually fix anything

`calibration_check.py` generates true-null data (iid Gaussian features, cosine similarity, replicate retrieval: `M = n_rep - 1` positives against `n_ctl` controls) and asks two questions.
Numbers below are from a run at the documented defaults: 20,000 true-null simulations per config, 400,000 null draws resampled from a pool of 2,000,000 exact-law APs.

**Prediction.** The predicted design effect tracks the measured variance inflation across a 28x range of pairwise correlation.

| n_rep | n_ctl | M | L | rho_pred | rho_meas | DE_pred | DE_meas | ratio |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 3 | 20 | 2 | 22 | +0.3687 | +0.3778 | 1.7375 | 1.7795 +- 0.0275 | 1.024 |
| 4 | 20 | 3 | 23 | +0.2396 | +0.2587 | 1.7187 | 1.7660 +- 0.0235 | 1.028 |
| 6 | 20 | 5 | 25 | +0.1362 | +0.1425 | 1.6811 | 1.6910 +- 0.0202 | 1.006 |
| 10 | 20 | 9 | 29 | +0.0678 | +0.0746 | 1.6101 | 1.6725 +- 0.0190 | 1.039 |
| 4 | 100 | 3 | 103 | +0.2709 | +0.2800 | 1.8126 | 1.8282 +- 0.0377 | 1.009 |
| 10 | 100 | 9 | 109 | +0.0891 | +0.0990 | 1.8016 | 1.8945 +- 0.0238 | 1.052 |
| 20 | 100 | 19 | 119 | +0.0403 | +0.0467 | 1.7659 | 1.8808 +- 0.0211 | 1.065 |
| 30 | 50 | 29 | 79 | +0.0205 | +0.0234 | 1.5939 | 1.6708 +- 0.0176 | 1.048 |
| 50 | 100 | 49 | 149 | +0.0131 | +0.0153 | 1.6401 | 1.7526 +- 0.0187 | 1.069 |

The theory sits 1 to 7 percent below the measured inflation, which is 2 to 6 Monte Carlo standard errors, so the gap is real rather than noise.
It is not a defect in the formula.
When the simulator is swapped for the exact model `cov_ap` assumes (every similarity iid, only the pair `(i, j)` shared between profiles `i` and `j`), the gap largely closes: measured DE 1.7377 / 1.5722 / 1.7744 against predicted 1.7187 / 1.6101 / 1.7659 at `(4,20)` / `(10,20)` / `(20,100)`, agreement within about 2 percent and within roughly 2 standard errors.
The residual few percent in the real cosine setting comes from all profiles being built out of the same feature draws, a coupling that lies outside the tier-2 model.

**Calibration.** False-positive rate on true-null data, ranges across the nine configurations:

| method | FPR at nominal 0.05 | FPR at nominal 0.01 |
| --- | --- | --- |
| independent null, uncorrected | 0.089 to 0.109 | 0.035 to 0.046 |
| corrected sd (this work) | 0.053 to 0.060 | 0.013 to 0.019 |
| oracle sd, measured from simulation | 0.052 to 0.059 | 0.012 to 0.016 |
| Normal approximation, corrected sd | 0.061 to 0.087 | 0.019 to 0.049 |

The correction removes most of the error: roughly a 2x over-rejection at alpha 0.05 becomes about 1.15x, and a 4x over-rejection at alpha 0.01 becomes about 1.6x.
It does **not** reach nominal.
The oracle row is the ceiling for any variance-only fix, and it misses nominal by almost exactly the same margin, which locates the residual in distribution shape rather than in the variance.
The diagnostics agree: the true mAP distribution is more right-skewed than the independent-convolution null at every configuration (for example 0.36 against 0.08 at `(50,100)`), and the empirical upper tail is 1.34 to 1.52 times wider than the independent null while a pure variance rescale can only deliver the sd ratio of 1.29 to 1.38.

## Limitations

The general variance formula is not proved in Lean.
It is verified by exhaustive enumeration up to `L = 12` and by `native_decide` inside Lean up to `L = 10`, which is strong evidence and not a proof.
What is missing is the `E[W^2]` identity: the four-way case split on which of the four indices coincide, plus double-sum harmonic identities such as `sum_{k<=L} H_k/k = (H_L^2 + H2_L)/2`.
The transfer machinery and the statement are already in place.

The covariance rests on a modelling assumption and cannot be checked against the ranking law alone, because the ranking law says nothing about two lists.
It is exact given the model, and the model is a simplification: in real Cell Painting style retrieval all profiles are built from the same feature matrix, which couples them beyond the single shared pair.
Empirically that extra coupling adds a few percent to the design effect, in the conservative direction (the correction under-inflates rather than over-inflates).

The correction is variance-only.
It does not fix skewness, so p-values in the far tail stay anti-conservative even after correction.
Anyone who needs calibrated inference at alpha 0.01 should permute rather than rely on these formulas.

`map_null_sd` on heterogeneous configs uses the exact heterogeneous covariance `cov_ap_hetero` for off-diagonal pairs (the former geometric-mean interpolation is gone).
Homogeneous configs are exact under the model; mixed ones are a guess.

Everything assumes binary relevance and a uniformly random ranking under the null.
Graded relevance and ties are out of scope.

`exact_map_pmf` is exact but its atom count grows with `n` and `L`; it is a tool for small configurations and for validating the moment formulas, not for production-scale `L`.

Relationship to `ap_distribution.py`: that notebook enumerates rank subsets directly to display the single-profile PMF interactively.
`ap_moments.py` reaches the same single-profile law through a polynomial-time dynamic program and extends it to the `n`-profile convolution, which enumeration cannot do.
The overlap is intentional and the two agree exactly (`test_exact_map_pmf_single_profile_matches_enumeration`).

## Reproducing

```
uv run --with pytest --with numpy python -m pytest test_ap_moments.py -q
uvx ruff check . && uvx ruff format --check .
cd lean && lake build
uv run ap_moments.py
uv run --with numpy calibration_check.py
```

`lake build` is expected to emit exactly one warning, the `sorry` at `lean/ap_moments.lean:556`.
The calibration run takes about half a minute at the defaults; `--validate` re-checks the fast simulator against copairs and needs `--with pandas --with copairs`.
