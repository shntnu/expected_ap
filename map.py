# /// script
# requires-python = ">=3.12"
# dependencies = [
#     "anthropic==0.66.0",
#     "marimo",
#     "matplotlib==3.10.6",
#     "numpy==2.1.3",
#     "pandas==2.3.2",
# ]
# ///

import marimo

__generated_with = "0.15.2"
app = marimo.App(width="columns")


@app.cell(column=0)
def _():
    return


@app.cell
def _():
    # ===============================================================
    # Highly annotated Python: Expected Mean AP under Random Ranking
    #   - Closed-form calculation (using harmonic numbers)
    #   - Monte Carlo simulation (random permutations)
    #   - Side-by-side comparison and a simple diagnostic plot
    #
    # This notebook-style script is self-contained and intended for
    # copy/paste into your notes. Every step includes detailed comments.
    # ===============================================================
    return


@app.cell
def _():
    import altair as alt
    import random
    import numpy as np
    import pandas as pd
    import matplotlib.pyplot as plt

    return alt, np, pd, plt, random


@app.cell
def _(np, random):
    # For reproducibility of all randomized pieces in this script.
    random.seed(123)
    np.random.seed(123)
    return


@app.cell
def _():
    # ---------------------------------------------------------------
    # PART A. DEFINITIONS
    # ---------------------------------------------------------------

    def harmonic_number(L: int) -> float:
        """
        Compute the L-th harmonic number, H_L = sum_{k=1}^L (1/k).
        - This appears in the closed-form expression for E[AP] (mu0).
        - For moderate L (<= a few million), direct summation is precise
          and fast enough for most notebook use-cases.
        """
        # Using a straightforward sum for clarity.
        return sum(1.0 / k for k in range(1, L + 1))

    def ap_mean_closed_form(M: int, N: int) -> float:
        """
        Closed-form expected AP (mu0) under a uniformly random ranking of L=M+N items
        containing M positives and N negatives.

        Derivation (succinct summary):
        - AP is the average of precision at each *positive* rank.
        - Using exchangeability and a hypergeometric argument for the number of positives
          preceding a given positive at rank r, one can show that
            E[AP] = (1/L) * [ ((M-1)/(L-1)) * (L - H_L) + H_L ]
          where H_L is the L-th harmonic number.

        This simplifies to the intuitive "prevalence + correction" form:
            E[AP] = (M/L) + (N / (L*(L-1))) * (H_L - 1)

        Notes:
        - This value is always slightly larger than prevalence M/L when N>0, and
          the difference vanishes as L grows (H_L ≈ log L + γ).
        """
        L = M + N
        if L < 1 or M < 0 or N < 0 or M > L:
            raise ValueError("Inputs must satisfy: L=M+N>=1, M>=0, N>=0, M<=L.")
        if (
            L == 1
        ):  # Trivial case: only one item (either AP=1 or AP=0 depending on label)
            return 1.0 if M == 1 else 0.0

        HL = harmonic_number(L)
        mu0 = (1.0 / L) * (((M - 1.0) / (L - 1.0)) * (L - HL) + HL)
        # Equivalent alternative form (should be numerically identical):
        # p = M / L
        # mu0_alt = p + (N / (L * (L - 1.0))) * (HL - 1.0)
        return mu0

    def ap_min_closed_form(M: int, N: int) -> float:
        """
        Worst-case AP when all positives are ranked after all negatives.
        Formula:
            AP_min = (1/M) * sum_{k=1..M} [ k / (N + k) ]
                   = 1 - (N/M) * (H_{N+M} - H_N)
        """
        if M <= 0:
            return 0.0
        HNm = harmonic_number(N + M)
        HN = harmonic_number(N)
        return 1.0 - (N / float(M)) * (HNm - HN)

    return ap_mean_closed_form, ap_min_closed_form


@app.cell
def _(np):
    def average_precision(labels: np.ndarray) -> float:
        """
        Compute *non-interpolated* Average Precision (AP) for a ranked list of binary labels.
        - Input: labels is a 1D numpy array of shape (L,), in ranked order from top (index 0)
          to bottom (index L-1). Values must be 0 (negative) or 1 (positive).
        - AP definition used:
            AP = mean of precisions at the ranks where a positive occurs.
          That is, if positives occur at ranks r_1 < r_2 < ... < r_M,
            AP = (1/M) * sum_{i=1..M} [ (#positives up to r_i) / r_i ]
          (here ranks are 1-based in the formula; we adjust for 0-based arrays)
        """
        # Total positives (M). If there are no positives, AP is conventionally 0.0.
        M = int(labels.sum())
        if M == 0:
            return 0.0

        # Running count of positives as we walk down the list.
        tp = 0
        precisions = []

        # Enumerate ranks in 1-based indexing for clarity in the precision formula.
        for k, y in enumerate(labels, start=1):
            if y == 1:
                tp += 1  # another true positive encountered
                precisions.append(tp / k)  # precision at this positive's rank

        # AP is the mean of those per-positive precisions.
        return float(np.mean(precisions)) if precisions else 0.0

    return (average_precision,)


@app.cell
def _(ap_mean_closed_form, ap_min_closed_form):
    def normalize_average_precision(
        AP_obs: float, M: int, N: int, onesided: bool = True
    ) -> float:
        """
        Normalized AP (n*-AP) in [-1, 1].
        - AP_obs: observed AP
        - M: number of positives
        - N: number of negatives
        - onesided: if True, normalize against [mu0, 1]; if False, two-sided
        """
        mu0 = ap_mean_closed_form(M, N)
        mn0 = ap_min_closed_form(M, N)

        if onesided:
            denom = 1.0 - mu0
        else:
            if AP_obs >= mu0:
                denom = 1.0 - mu0
            else:
                denom = mu0 - mn0

        return (AP_obs - mu0) / denom if denom > 0 else 0.0

    return (normalize_average_precision,)


@app.cell
def _(average_precision, np):
    def simulate_ap_stats(
        M: int, N: int, trials: int = 5000, seed: int = 42
    ) -> tuple[float, float]:
        """
        Monte Carlo estimate of E[AP] under random ranking.
        - Create a multiset of M ones (positives) and N zeros (negatives).
        - Repeatedly shuffle (uniformly at random), compute AP for each shuffle,
          and return (mean(AP), std(AP)).

        Parameters
        ----------
        M, N : int
            Number of positives and negatives, respectively.
        trials : int
            Number of random shuffles to average over.
        seed : int
            Seed for the RNG to ensure reproducible results.

        Returns
        -------
        (mu_hat, sd_hat) : tuple of floats
            Empirical mean and standard deviation of AP across trials.
        """
        if M < 0 or N < 0:
            raise ValueError("M and N must be nonnegative.")
        if M + N == 0:
            return (0.0, 0.0, 0.0)

        rng = np.random.default_rng(seed)
        base = np.array([1] * M + [0] * N, dtype=int)
        aps = np.empty(trials, dtype=float)

        for t in range(trials):
            rng.shuffle(base)  # in-place shuffle = new random ranking
            aps[t] = average_precision(base)

        return float(aps.mean()), float(aps.std()), float(aps.min())

    return (simulate_ap_stats,)


@app.cell
def _(ap_mean_closed_form, ap_min_closed_form, pd, simulate_ap_stats):
    # ---------------------------------------------------------------
    # PART B. DEMONSTRATION / VALIDATION
    #   - Choose several (L, prevalence) settings.
    #   - For each: compute the closed-form prediction (mu0) and the
    #     Monte Carlo estimate, then compare.
    # ---------------------------------------------------------------

    # A small grid of list sizes and prevalences (feel free to edit).
    Ls = [50, 100, 200, 500, 1000, 2000]
    prevalences = [0.05, 0.20, 0.50]  # M/L choices
    trials = 6000  # number of Monte Carlo shuffles per setting

    rows = []
    for L in Ls:
        for p in prevalences:
            # Convert prevalence to integer counts M and N.
            # We round to the nearest integer to keep M an integer in [1, L-1] when possible.
            M = max(1, min(L - 1, int(round(p * L))))
            N = L - M
            p_eff = M / L  # actual prevalence after rounding

            # Closed-form theoretical mean (mu0)
            mu_pred = ap_mean_closed_form(M, N)

            # Closed-form theoretical min (mn0)
            mn_pred = ap_min_closed_form(M, N)

            # Monte Carlo estimate
            mu_sim, sd_sim, mn_sim = simulate_ap_stats(M, N, trials=trials, seed=2025)

            rows.append(
                {
                    "L": L,
                    "M": M,
                    "N": N,
                    "prev (M/L)": p_eff,
                    "pred_mu0": mu_pred,
                    "sim_mu0": mu_sim,
                    "abs_error_mu0": abs(mu_sim - mu_pred),
                    "pred_mn0": mn_pred,
                    "sim_mn0": mn_sim,
                    "abs_error_mn0": abs(mn_sim - mn_pred),
                    "trials": trials,
                }
            )

    df = pd.DataFrame(rows)
    return (df,)


@app.cell
def _(df):
    df
    return


@app.cell
def _(df, np, plt):
    # ---------------------------------------------------------------
    # PART C. DIAGNOSTIC PLOT
    #   - Plot predicted vs. simulated mean AP and a y=x reference line.
    # ---------------------------------------------------------------

    plt.figure(figsize=(6, 6))
    plt.scatter(df["pred_mu0"], df["sim_mu0"])
    mn_mu0 = min(df["pred_mu0"].min(), df["sim_mu0"].min())
    mx_mu0 = max(df["pred_mu0"].max(), df["sim_mu0"].max())
    grid_mu0 = np.linspace(mn_mu0, mx_mu0, 200)
    plt.plot(grid_mu0, grid_mu0)  # y = x line
    plt.xlabel("Predicted E[AP] (closed-form)")
    plt.ylabel("Simulated mean AP")
    plt.title("Random-ranking AP: Predicted vs Simulated")
    plt.tight_layout()
    plt.show()
    return


@app.cell
def _(df, np, plt):
    plt.figure(figsize=(6, 6))
    plt.scatter(df["pred_mn0"], df["sim_mn0"])
    mn_mn0 = min(df["pred_mn0"].min(), df["sim_mn0"].min())
    mx_mn0 = max(df["pred_mn0"].max(), df["sim_mn0"].max())
    grid_mn0 = np.linspace(mn_mn0, mx_mn0, 200)
    plt.plot(grid_mn0, grid_mn0)  # y = x line
    plt.xlabel("Predicted min(AP) (closed-form)")
    plt.ylabel("Simulated min AP")
    plt.title("Random-ranking AP: Predicted vs Simulated")
    plt.tight_layout()
    plt.show()
    return


@app.cell
def _():
    # Settings to test
    cases = [(3, 7), (5, 95), (10, 90), (20, 180), (50, 450)]
    return (cases,)


@app.cell
def _(
    ap_mean_closed_form,
    ap_min_closed_form,
    average_precision,
    cases,
    normalize_average_precision,
    np,
    pd,
    simulate_normalized_scores,
):
    def compute_normalized_ap_diagnostics():
        results = []
        for M, N in cases:
            aps, scores, scores_normalized = simulate_normalized_scores(
                M, N, trials=8000, seed=2025
            )
            mu0 = ap_mean_closed_form(M, N)
            apmin = ap_min_closed_form(M, N)

            # Automated checks
            min_sc, max_sc = float(scores.min()), float(scores.max())
            within_bounds = (min_sc >= -1 - 1e-9) and (max_sc <= 1 + 1e-9)
            # Check anchors programmatically
            # Construct exact AP_min configuration (positives at bottom) and AP=1 (positives at top)
            L = M + N
            pos_bottom = np.array([0] * N + [1] * M, dtype=int)
            pos_top = np.array([1] * M + [0] * N, dtype=int)
            ap_bot = average_precision(pos_bottom)
            ap_top = average_precision(pos_top)

            nstar_bot = normalize_average_precision(ap_bot, M, N)
            nstar_top = normalize_average_precision(ap_top, M, N)
            nstar_mu0 = normalize_average_precision(mu0, M, N)

            results.append(
                {
                    "M": M,
                    "N": N,
                    "L": L,
                    "mu0": mu0,
                    "AP_min": apmin,
                    "min(normalized)": min_sc,
                    "max(normalized)": max_sc,
                    "within [-1,1]?": within_bounds,
                    "n*(AP_min)": nstar_bot,
                    "n*(AP=1)": nstar_top,
                    "n*(AP=mu0)": nstar_mu0,
                }
            )

        df = pd.DataFrame(results)
        return (df,)

    return (compute_normalized_ap_diagnostics,)


@app.cell
def _(compute_normalized_ap_diagnostics):
    compute_normalized_ap_diagnostics()
    return


@app.cell(column=1)
def _(average_precision, normalize_average_precision, np):
    def simulate_normalized_scores(
        M: int, N: int, trials: int = 10000, seed: int = 7, onesided=False
    ):
        """Simulate AP and normalized scores for random rankings."""
        rng = np.random.default_rng(seed)
        base = np.array([1] * M + [0] * N, dtype=int)
        scores = np.empty(trials, dtype=float)
        scores_normalized = np.empty(trials, dtype=float)
        aps = np.empty(trials, dtype=float)
        for t in range(trials):
            rng.shuffle(base)
            ap = average_precision(base)
            aps[t] = ap
            scores[t] = ap
            scores_normalized[t] = normalize_average_precision(
                ap, M, N, onesided=onesided
            )
        return aps, scores, scores_normalized

    return (simulate_normalized_scores,)


@app.cell
def _(
    alt,
    ap_mean_closed_form,
    ap_min_closed_form,
    normalize_average_precision,
    pd,
    simulate_normalized_scores,
):
    def plot_sample_aps(onesided):
        # Visualization: histogram of normalized scores for a couple of cases
        chart_columns = []
        for M, N in [(3, 7), (5, 95), (10, 90), (20, 180)]:
            _, scores, scores_normalized = simulate_normalized_scores(
                M, N, trials=20000, seed=11, onesided=onesided
            )

            mu0 = ap_mean_closed_form(M, N)

            mn0 = ap_min_closed_form(M, N)

            mu0_normalized = normalize_average_precision(mu0, M, N, onesided=onesided)

            mn0_normalized = normalize_average_precision(mn0, M, N, onesided=onesided)

            # Create dataframe for Altair
            df = pd.DataFrame({"AP": scores, "n*-AP": scores_normalized})

            # Helper function to create histogram with vertical lines
            def make_histogram(
                data_col, title_suffix, vline_values, vline_labels, x_domain=None
            ):
                x_encoding = alt.X(
                    f"{data_col}:Q", bin=alt.Bin(maxbins=50), title=data_col
                )
                if x_domain:
                    x_encoding = alt.X(
                        f"{data_col}:Q",
                        bin=alt.Bin(maxbins=50),
                        title=data_col,
                        scale=alt.Scale(domain=x_domain),
                    )

                bars = (
                    alt.Chart(df)
                    .mark_bar()
                    .encode(
                        x=x_encoding,
                        y=alt.Y("count()", title="Frequency"),
                        tooltip=["count()", alt.Tooltip(f"{data_col}:Q", bin=True)],
                    )
                )

                vline_df = pd.DataFrame({"value": vline_values, "label": vline_labels})

                vlines = (
                    alt.Chart(vline_df)
                    .mark_rule(strokeDash=[5, 5])
                    .encode(
                        x="value:Q",
                        color=alt.Color(
                            "label:N",
                            scale=alt.Scale(domain=vline_labels, range=["blue", "red"]),
                        ),
                        strokeWidth=alt.value(2),
                    )
                )

                return (bars + vlines).properties(
                    width=400, height=180, title=f"{title_suffix} (M={M}, N={N})"
                )

            # Create both histograms using the helper
            chart_normalized = make_histogram(
                "n*-AP",
                "Normalized AP",
                [mu0_normalized, mn0_normalized],
                ["E[n*-AP]", "n*-AP_min"],
            )

            chart_regular = make_histogram(
                "AP", "Regular AP", [mu0, mn0], ["E[AP]", "AP_min"]
            )

            # Create scatter plot with reference lines
            chart_scatter_points = (
                alt.Chart(df)
                .mark_circle(size=20, opacity=0.5)
                .encode(
                    x=alt.X("AP:Q", title="AP", scale=alt.Scale(domain=[0, 1])),
                    y=alt.Y("n*-AP:Q", title="n*-AP", scale=alt.Scale(domain=[-1, 1])),
                    tooltip=["AP:Q", "n*-AP:Q"],
                )
            )

            # Create reference lines data
            ref_lines_data = pd.DataFrame(
                {
                    "x_val": [mu0, mn0, None, None],
                    "y_val": [None, None, mu0_normalized, mn0_normalized],
                    "label": ["E[AP]", "AP_min", "E[n*-AP]", "n*-AP_min"],
                    "type": ["vertical", "vertical", "horizontal", "horizontal"],
                }
            )

            # Vertical reference lines
            vlines_df = ref_lines_data[ref_lines_data["type"] == "vertical"].dropna(
                subset=["x_val"]
            )
            chart_vlines = (
                alt.Chart(vlines_df)
                .mark_rule(strokeDash=[5, 5])
                .encode(
                    x="x_val:Q",
                    color=alt.Color(
                        "label:N",
                        scale=alt.Scale(
                            domain=["E[AP]", "AP_min", "E[n*-AP]", "n*-AP_min"],
                            range=["blue", "red", "blue", "red"],
                        ),
                    ),
                    strokeWidth=alt.value(2),
                )
            )

            # Horizontal reference lines
            hlines_df = ref_lines_data[ref_lines_data["type"] == "horizontal"].dropna(
                subset=["y_val"]
            )
            chart_hlines = (
                alt.Chart(hlines_df)
                .mark_rule(strokeDash=[5, 5])
                .encode(
                    y="y_val:Q",
                    color=alt.Color(
                        "label:N",
                        scale=alt.Scale(
                            domain=["E[AP]", "AP_min", "E[n*-AP]", "n*-AP_min"],
                            range=["blue", "red", "blue", "red"],
                        ),
                    ),
                    strokeWidth=alt.value(2),
                )
            )

            chart_scatter = (
                chart_scatter_points + chart_vlines + chart_hlines
            ).properties(width=180, height=180, title=f"AP vs n*-AP (M={M}, N={N})")

            # Stack the three charts vertically for this (M,N) pair
            chart_columns.append(
                alt.hconcat(chart_normalized, chart_regular, chart_scatter)
            )

        # Arrange columns horizontally
        return alt.vconcat(*chart_columns)

    return (plot_sample_aps,)


@app.cell
def _(plot_sample_aps):
    plot_sample_aps(onesided=True)
    return


@app.cell
def _(plot_sample_aps):
    plot_sample_aps(onesided=False)
    return


if __name__ == "__main__":
    app.run()
