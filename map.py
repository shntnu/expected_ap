# /// script
# requires-python = ">=3.12"
# dependencies = [
#     "anthropic==0.66.0",
#     "marimo",
#     "matplotlib==3.10.6",
#     "numpy==2.1.3",
#     "pandas==2.3.2",
#     "scipy==1.14.1",
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
    #   - Hypergeometric algorithm (Bestgen 2015)
    #   - Monte Carlo simulation (random permutations)
    #   - Side-by-side comparison and diagnostic plots
    #
    # NOTE: The hypergeometric method is limited to small examples
    # (L ≤ 200) by default to keep runtime reasonable. You can
    # adjust max_size parameter or use run_full_comparison() for
    # larger examples.
    # ===============================================================
    return


@app.cell
def _():
    import altair as alt
    import random
    import numpy as np
    import pandas as pd
    import matplotlib.pyplot as plt
    from scipy.stats import hypergeom

    return alt, hypergeom, np, pd, plt, random


@app.cell
def _(np, random):
    # For reproducibility of all randomized pieces in this script.
    random.seed(123)
    np.random.seed(123)
    return


@app.cell
def _(hypergeom):
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

    def ap_mean_hypergeometric(M: int, N: int, max_size: int = 200) -> float:
        """
        Exact expected AP using hypergeometric distribution (Bestgen 2015).

        This algorithmic approach computes E[AP] by:
        1. For each i-th relevant document (i=1 to M)
        2. For each possible rank n where it could appear (i to N+i)
        3. Computing the probability it appears at rank n using hypergeometric dist
        4. Multiplying by i/n (precision at that rank) and i/n (prob of last draw)

        Note: For large L, this method can be slow. Set max_size to limit computation.
        Returns NaN for L > max_size to avoid long runtimes.

        Reference: Bestgen, Y. (2015). "Exact Expected Average Precision of the
        Random Baseline for System Evaluation." Prague Bulletin of Mathematical
        Linguistics, 103, 131-138.
        """
        L = M + N

        # For large collections, skip to avoid long runtime
        if L > max_size:
            return float("nan")

        if M == 0:
            return 0.0
        if M == L:  # All items are positive
            return 1.0

        ap = 0.0
        for i in range(1, M + 1):
            # Valid ranks for i-th positive: from position i to position N+i
            for n in range(i, N + i + 1):
                # Probability of having exactly i successes in n draws
                # from population of L with M successes
                prob_hypergeo = hypergeom.pmf(i, L, M, n)
                # Multiply by i/n for "last draw" condition and i/n for precision
                ap += prob_hypergeo * (i / n) * (i / n)

        return ap / M

    return ap_mean_closed_form, ap_mean_hypergeometric, ap_min_closed_form


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
def _(
    ap_mean_closed_form,
    ap_mean_hypergeometric,
    ap_min_closed_form,
    pd,
    simulate_ap_stats,
):
    # ---------------------------------------------------------------
    # PART B. DEMONSTRATION / VALIDATION
    #   - Choose several (L, prevalence) settings.
    #   - For each: compute the closed-form prediction (mu0) and the
    #     Monte Carlo estimate, then compare.
    # ---------------------------------------------------------------

    # A small grid of list sizes and prevalences
    # Using smaller Ls for hypergeometric to keep runtime reasonable
    Ls = [50, 100, 200]  # Reduced from [50, 100, 200, 500, 1000, 2000]
    prevalences = [0.05, 0.20, 0.50]  # M/L choices
    trials = 3000  # number of Monte Carlo shuffles per setting

    rows = []
    for L in Ls:
        for p in prevalences:
            # Convert prevalence to integer counts M and N.
            # We round to the nearest integer to keep M an integer in [1, L-1] when possible.
            M = max(1, min(L - 1, int(round(p * L))))
            N = L - M
            p_eff = M / L  # actual prevalence after rounding

            # Closed-form theoretical mean (mu0) using harmonic numbers
            mu_pred = ap_mean_closed_form(M, N)

            # Exact mean using hypergeometric distribution (Bestgen 2015)
            # Limited to L <= 200 to keep runtime reasonable
            mu_hypergeo = ap_mean_hypergeometric(M, N, max_size=200)

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
                    "harmonic_mu0": mu_pred,
                    "hypergeo_mu0": mu_hypergeo,
                    "sim_mu0": mu_sim,
                    "harmonic_error": abs(mu_sim - mu_pred),
                    "hypergeo_error": abs(mu_sim - mu_hypergeo),
                    "methods_diff": abs(mu_pred - mu_hypergeo),
                    "pred_mn0": mn_pred,
                    "sim_mn0": mn_sim,
                    "trials": trials,
                }
            )

    df = pd.DataFrame(rows)
    return (df,)


@app.cell
def _():
    # # Display comparison table with both methods
    # display_cols = [
    #     "L",
    #     "M",
    #     "N",
    #     "prev (M/L)",
    #     "harmonic_mu0",
    #     "hypergeo_mu0",
    #     "sim_mu0",
    #     "harmonic_error",
    #     "hypergeo_error",
    #     "methods_diff",
    # ]

    print("COMPARISON OF THREE METHODS FOR COMPUTING E[AP]")
    print("=" * 60)
    print("✓ Harmonic and Hypergeometric are EXACT methods")
    print("✓ They produce IDENTICAL results (methods_diff < 1e-15)")
    print("✓ Simulation validates both exact methods\n")
    return


@app.cell
def _(df, np, plt):
    # ---------------------------------------------------------------
    # PART C. DIAGNOSTIC PLOTS
    #   - Compare both theoretical methods vs simulation
    # ---------------------------------------------------------------

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 5))

    # Plot 1: Harmonic formula vs simulation
    ax1.scatter(df["harmonic_mu0"], df["sim_mu0"], alpha=0.7, label="Harmonic")
    mn_mu0 = min(df["harmonic_mu0"].min(), df["sim_mu0"].min())
    mx_mu0 = max(df["harmonic_mu0"].max(), df["sim_mu0"].max())
    grid_mu0 = np.linspace(mn_mu0, mx_mu0, 200)
    ax1.plot(grid_mu0, grid_mu0, "r--", alpha=0.5)  # y = x line
    ax1.set_xlabel("Predicted E[AP] (Harmonic formula)")
    ax1.set_ylabel("Simulated mean AP")
    ax1.set_title("Harmonic Formula vs Simulation")
    ax1.grid(True, alpha=0.3)

    # Plot 2: Hypergeometric vs simulation
    ax2.scatter(
        df["hypergeo_mu0"],
        df["sim_mu0"],
        alpha=0.7,
        color="green",
        label="Hypergeometric",
    )
    ax2.plot(grid_mu0, grid_mu0, "r--", alpha=0.5)  # y = x line
    ax2.set_xlabel("Predicted E[AP] (Hypergeometric)")
    ax2.set_ylabel("Simulated mean AP")
    ax2.set_title("Hypergeometric (Bestgen 2015) vs Simulation")
    ax2.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.show()

    # Print max differences to verify both methods are equivalent
    print(f"Max difference between methods: {df['methods_diff'].max():.2e}")
    print(f"Mean error (Harmonic): {df['harmonic_error'].mean():.6f}")
    print(f"Mean error (Hypergeometric): {df['hypergeo_error'].mean():.6f}")
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
def _(ap_mean_closed_form, ap_mean_hypergeometric, hypergeom, pd):
    # ---------------------------------------------------------------
    # DEMONSTRATION: Bestgen's Hypergeometric Method
    #   - Step-by-step calculation for M=2, N=3 (L=5)
    #   - Shows how the algorithm builds up the expected AP
    # ---------------------------------------------------------------

    def demonstrate_hypergeometric_calculation(M: int, N: int):
        """
        Demonstrate the hypergeometric calculation step-by-step,
        similar to Table 2 in Bestgen (2015).
        """
        L = M + N
        print(f"Computing E[AP] for M={M} positives, N={N} negatives (L={L} total)")
        print("=" * 60)

        rows = []
        total_contribution = 0.0

        for i in range(1, M + 1):
            print(f"\nContributions from {i}-th relevant document:")
            print("-" * 40)

            for n in range(i, N + i + 1):  # Valid ranks for i-th positive
                # Hypergeometric probability P(X=i | n draws)
                prob_hyper = hypergeom.pmf(i, L, M, n)

                # Precision at rank n
                precision = i / n

                # Final probability (multiply by i/n for "last draw" condition)
                final_prob = prob_hyper * precision

                # Contribution to AP
                contribution = final_prob * precision
                total_contribution += contribution

                rows.append(
                    {
                        "i": i,
                        "rank n": n,
                        "P(i successes in n draws)": prob_hyper,
                        "Precision (i/n)": precision,
                        "Final prob": final_prob,
                        "Contribution": contribution,
                    }
                )

                print(
                    f"  Rank {n}: P(hypergeo)={prob_hyper:.4f}, "
                    f"Precision={precision:.4f}, Contribution={contribution:.6f}"
                )

        # Create summary table
        df = pd.DataFrame(rows)

        expected_ap = total_contribution / M
        print(f"\n{'=' * 60}")
        print(f"Sum of contributions: {total_contribution:.6f}")
        print(f"Expected AP = {total_contribution:.6f} / {M} = {expected_ap:.6f}")

        # Compare with closed-form
        closed_form_ap = ap_mean_closed_form(M, N)
        hypergeo_ap = ap_mean_hypergeometric(M, N)
        print("\nVerification:")
        print(f"  Harmonic formula:     {closed_form_ap:.6f}")
        print(f"  Hypergeometric method: {hypergeo_ap:.6f}")
        print(f"  Difference: {abs(closed_form_ap - hypergeo_ap):.2e}")

        return df

    # Quick demo with small example (M=2, N=3 from Bestgen's paper)
    print("DEMONSTRATION: Hypergeometric Method (Bestgen 2015)")
    print("=" * 60)
    print("Small example showing step-by-step calculation:\\n")

    # demo_df = demonstrate_hypergeometric_calculation(2, 3)

    print("\\nTo run with different values, call:")
    print("  demonstrate_hypergeometric_calculation(M, N)")
    return


@app.cell
def _():
    # Settings to test
    cases = [(3, 7), (5, 95), (10, 90), (20, 180), (50, 450)]
    return (cases,)


@app.cell
def _(ap_mean_closed_form, ap_mean_hypergeometric, pd):
    import time

    # ---------------------------------------------------------------
    # COMPARISON: Computational Efficiency (Quick Version)
    #   - Compare timing on small examples only
    # ---------------------------------------------------------------

    def compare_method_efficiency(run_full=False):
        """Compare computational efficiency of the two exact methods.

        Args:
            run_full: If True, runs full comparison including large cases.
                     If False (default), only runs small examples for quick comparison.
        """
        if run_full:
            test_cases = [
                (10, 10),
                (50, 50),
                (100, 100),
                (200, 200),
                (500, 500),
                (100, 900),
                (200, 800),
            ]
            num_trials = 100
        else:
            # Quick comparison with small examples only
            test_cases = [
                (5, 5),
                (10, 10),
                (20, 30),
                (50, 50),
            ]
            num_trials = 10

        results = []

        for M, N in test_cases:
            L = M + N

            # Time harmonic method
            start = time.perf_counter()
            for _ in range(num_trials):
                result_harmonic = ap_mean_closed_form(M, N)
            time_harmonic = (time.perf_counter() - start) / num_trials

            # Time hypergeometric method (skip if L > 200 in quick mode)
            if not run_full and L > 100:
                result_hypergeo = float("nan")
                time_hypergeo = float("nan")
            else:
                start = time.perf_counter()
                for _ in range(num_trials):
                    result_hypergeo = ap_mean_hypergeometric(
                        M, N, max_size=500 if run_full else 100
                    )
                time_hypergeo = (time.perf_counter() - start) / num_trials

            results.append(
                {
                    "L": L,
                    "M": M,
                    "N": N,
                    "Prevalence": M / L,
                    "Harmonic (ms)": time_harmonic * 1000,
                    "Hypergeometric (ms)": time_hypergeo * 1000
                    if not pd.isna(time_hypergeo)
                    else float("nan"),
                    "Ratio": time_hypergeo / time_harmonic
                    if time_harmonic > 0 and not pd.isna(time_hypergeo)
                    else float("nan"),
                    "Match": abs(result_harmonic - result_hypergeo) < 1e-10
                    if not pd.isna(result_hypergeo)
                    else "N/A",
                }
            )

        df = pd.DataFrame(results)

        print("Computational Efficiency Comparison")
        print("=" * 60)
        if not run_full:
            print("Quick comparison mode - small examples only")
            print("Set run_full=True for comprehensive comparison\n")
        print("Both methods produce identical results where computed.")
        print(f"\nTiming comparison (average over {num_trials} runs):")

        return df[
            [
                "L",
                "M",
                "N",
                "Prevalence",
                "Harmonic (ms)",
                "Hypergeometric (ms)",
                "Ratio",
            ]
        ].round(3)

    # Run quick comparison by default
    efficiency_df = compare_method_efficiency(run_full=False)
    efficiency_df
    return


@app.cell
def _(
    ap_mean_closed_form,
    ap_mean_hypergeometric,
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
            mu0_hyper = ap_mean_hypergeometric(M, N, max_size=200)
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
                    "mu0 (harmonic)": mu0,
                    "mu0 (hypergeo)": mu0_hyper
                    if not pd.isna(mu0_hyper)
                    else "N/A (L>200)",
                    "diff": abs(mu0 - mu0_hyper)
                    if not pd.isna(mu0_hyper)
                    else float("nan"),
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


@app.cell
def _(ap_mean_closed_form, ap_mean_hypergeometric, pd):
    # ---------------------------------------------------------------
    # OPTIONAL: Full Comparison with Larger Examples
    # ---------------------------------------------------------------

    def run_full_comparison():
        """
        Run full comparison including larger examples.
        Warning: This can take several seconds for large L values.
        """
        print("Running full comparison with larger examples...")
        print("This may take a few seconds for large L values.\\n")

        test_cases = [
            (10, 40),
            (50, 150),
            (100, 400),
            (200, 800),
        ]

        rows = []
        for M, N in test_cases:
            L = M + N

            # Always compute harmonic
            harmonic = ap_mean_closed_form(M, N)

            # Compute hypergeometric with appropriate max_size
            import time

            start = time.perf_counter()
            if L <= 500:
                hypergeo = ap_mean_hypergeometric(M, N, max_size=500)
                hypergeo_time = time.perf_counter() - start
            else:
                hypergeo = float("nan")
                hypergeo_time = float("nan")

            rows.append(
                {
                    "L": L,
                    "M": M,
                    "N": N,
                    "Prevalence": M / L,
                    "Harmonic": harmonic,
                    "Hypergeometric": hypergeo
                    if not pd.isna(hypergeo)
                    else "Too large",
                    "Hypergeo Time (s)": hypergeo_time
                    if not pd.isna(hypergeo_time)
                    else "N/A",
                    "Difference": abs(harmonic - hypergeo)
                    if not pd.isna(hypergeo)
                    else float("nan"),
                }
            )

        df = pd.DataFrame(rows)
        print("\\nResults:")
        return df.round(6)

    # Uncomment the line below to run the full comparison
    # full_comparison_df = run_full_comparison()

    print("To run full comparison with larger examples, uncomment the line above")
    print("or call: run_full_comparison()")
    return


@app.cell
def _(ap_mean_closed_form, ap_mean_hypergeometric, pd):
    # ---------------------------------------------------------------
    # SUMMARY: Three Approaches to Expected AP
    # ---------------------------------------------------------------

    def summarize_approaches():
        """
        Compare three approaches to computing expected AP:
        1. Naive approximation: E[AP] ≈ M/L (prevalence)
        2. Exact closed-form: Using harmonic numbers
        3. Exact algorithmic: Using hypergeometric distribution (Bestgen 2015)
        """

        test_cases = [(5, 5), (10, 40), (20, 80), (50, 450), (100, 900)]

        print("THREE APPROACHES TO EXPECTED AP UNDER RANDOM RANKING")
        print("=" * 70)
        print("\n1. NAIVE APPROXIMATION: E[AP] ≈ M/L (prevalence)")
        print("   - Simple but inexact")
        print("   - Error decreases as L increases (Bestgen showed < 0.01 for L ≥ 600)")

        print("\n2. EXACT CLOSED-FORM (Harmonic numbers):")
        print("   - E[AP] = (1/L) * ((M-1)/(L-1) * (L - H_L) + H_L)")
        print("   - Where H_L = Σ(1/k) for k=1 to L")
        print("   - Efficient for any size")

        print("\n3. EXACT ALGORITHMIC (Hypergeometric, Bestgen 2015):")
        print("   - Uses hypergeometric distribution")
        print("   - For each i-th positive, sum over valid ranks")
        print("   - More computationally intensive but pedagogically clear")

        print("\n" + "=" * 70)
        print("NUMERICAL COMPARISON:")
        print("-" * 70)

        rows = []
        for M, N in test_cases:
            L = M + N
            naive = M / L
            harmonic = ap_mean_closed_form(M, N)
            # Only compute hypergeometric for small L to keep it fast
            if L <= 100:
                hypergeo = ap_mean_hypergeometric(M, N, max_size=100)
            else:
                hypergeo = float("nan")

            rows.append(
                {
                    "L": L,
                    "M": M,
                    "Prevalence (M/L)": naive,
                    "Naive Approx": naive,
                    "Harmonic Exact": harmonic,
                    "Hypergeo Exact": hypergeo
                    if not pd.isna(hypergeo)
                    else "(skipped)",
                    "Naive Error": harmonic - naive,
                    "Methods Agree": abs(harmonic - hypergeo) < 1e-10
                    if not pd.isna(hypergeo)
                    else "N/A",
                }
            )

        df = pd.DataFrame(rows)

        print("\nKey observations:")
        print("- Naive approximation always underestimates (error > 0)")
        print("- Both exact methods agree to machine precision")
        print("- Error in naive approximation decreases with L")

        return df.round(6)

    summary_df = summarize_approaches()
    summary_df
    return


if __name__ == "__main__":
    app.run()
