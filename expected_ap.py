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


@app.cell
def _(mo):
    mo.md(
        r"""
    # Expected Average Precision Under Random Ranking

    Interactive supplement demonstrating:

    1. Exact finite-sample formula via harmonic numbers
    2. Equivalence with Bestgen's (2015) hypergeometric method
    3. Asymptotic O(log L/L) convergence
    4. Statistical testing implications
    """
    )
    return


@app.cell
def _():
    import marimo as mo

    return (mo,)


@app.cell
def _():
    # Core imports
    import numpy as np
    import pandas as pd
    from scipy.stats import hypergeom
    import altair as alt

    # Set random seed for reproducibility
    np.random.seed(42)
    return alt, hypergeom, np, pd


@app.cell
def _(mo):
    mo.md(
        """
    ## Section 1: Core Definitions

    Average Precision (AP) for a ranking with M relevant items out of L total:

    $$\\text{AP} = \\frac{1}{M} \\sum_{k: y_k=1} \\text{Prec}@k$$
    """
    )
    return


@app.cell
def _(np):
    def average_precision(labels: np.ndarray) -> float:
        """
        Compute Average Precision for a ranked list of binary labels.

        Definition 1 from paper: AP is the mean of precisions at ranks
        where relevant items occur.
        """
        M = int(labels.sum())
        if M == 0:
            return 0.0

        tp = 0
        precisions = []

        for k, y in enumerate(labels, start=1):
            if y == 1:
                tp += 1
                precisions.append(tp / k)

        return float(np.mean(precisions))

    def harmonic_number(L: int) -> float:
        """Compute the L-th harmonic number H_L = Σ(1/k) for k=1 to L."""
        return sum(1.0 / k for k in range(1, L + 1))

    return average_precision, harmonic_number


@app.cell
def _(mo):
    mo.md(
        """
    ## Section 2: Main Result - Closed Form

    Under uniformly random ranking:

    $$\\mathbb{E}[\\text{AP}] = \\frac{1}{L}\\left[\\frac{M-1}{L-1}(L-H_L) + H_L\\right]$$

    Alternative form:

    $$\\mathbb{E}[\\text{AP}] = p + \\frac{N(H_L - 1)}{L(L-1)}$$

    where $p = M/L$ is the prevalence. This shows E[AP] > p for finite samples.
    """
    )
    return


@app.cell
def _(harmonic_number):
    def expected_ap_closed_form(M: int, N: int) -> float:
        """
        Closed-form expected AP under random ranking.
        Uses harmonic numbers for exact finite-sample calculation.
        """
        L = M + N
        if L < 1 or M < 0 or N < 0:
            raise ValueError("Invalid inputs")
        if L == 1:
            return 1.0 if M == 1 else 0.0

        H_L = harmonic_number(L)
        mu0 = (1.0 / L) * (((M - 1.0) / (L - 1.0)) * (L - H_L) + H_L)
        return mu0

    def expected_ap_prevalence_form(M: int, N: int) -> float:
        """
        Prevalence-plus-correction form.
        Shows explicitly that E[AP] = p + positive_bias_term.
        """
        L = M + N
        if L <= 1:
            return M / L if L > 0 else 0.0

        p = M / L
        H_L = harmonic_number(L)
        correction = (N / (L * (L - 1.0))) * (H_L - 1.0)
        return p + correction

    return (expected_ap_closed_form,)


@app.cell
def _(mo):
    mo.md(
        """
    ## Section 3: Bestgen's (2015) Hypergeometric Method

    Bestgen (2015) first identified that E[AP] ≠ prevalence and provided this exact calculation:

    $$\\mathbb{E}[\\text{AP}] = \\frac{1}{M} \\sum_{i=1}^{M} \\sum_{n=i}^{N+i} P_{\\text{hyper}}(i; L, M, n) \\cdot \\left(\\frac{i}{n}\\right)^2$$
    """
    )
    return


@app.cell
def _(hypergeom):
    def expected_ap_hypergeometric(M: int, N: int, max_L: int = 200) -> float:
        """
        Bestgen (2015): Exact expected AP using hypergeometric distribution.
        Limited to L ≤ max_L for computational efficiency.
        """
        L = M + N
        if L > max_L:
            return float("nan")
        if M == 0:
            return 0.0
        if M == L:
            return 1.0

        ap = 0.0
        for i in range(1, M + 1):
            for n in range(i, N + i + 1):
                prob_hyper = hypergeom.pmf(i, L, M, n)
                ap += prob_hyper * (i / n) * (i / n)

        return ap / M

    return (expected_ap_hypergeometric,)


@app.cell
def _(mo):
    mo.md(
        """
    ## Section 4: Validation - Both Methods Are Equivalent

    Demonstrating that the harmonic formula and hypergeometric algorithm produce identical results.
    """
    )
    return


@app.cell
def _(expected_ap_closed_form, expected_ap_hypergeometric, pd):
    def _():
        # Validate equivalence of both methods
        validation_cases = [
            (2, 3),  # Bestgen's Table 2 example
            (5, 5),
            (10, 40),
            (20, 80),
            (50, 150),
        ]

        validation_results = []
        for M, N in validation_cases:
            L = M + N
            harmonic = expected_ap_closed_form(M, N)
            hypergeo = expected_ap_hypergeometric(M, N)

            validation_results.append(
                {
                    "L": L,
                    "M": M,
                    "N": N,
                    "Prevalence": M / L,
                    "Harmonic Method": harmonic,
                    "Hypergeometric Method": hypergeo,
                    "Difference": abs(harmonic - hypergeo),
                    "Match": "✓" if abs(harmonic - hypergeo) < 1e-10 else "✗",
                }
            )

        validation_df = pd.DataFrame(validation_results)
        return validation_df

    _()
    return


@app.cell
def _(mo):
    mo.md(
        """
    ## Section 5: Reproducing Bestgen's Table 2

    Step-by-step calculation for M=2, N=3 (from Bestgen 2015).
    """
    )
    return


@app.cell
def _(expected_ap_closed_form, hypergeom, pd):
    def _():
        # Reproduce Bestgen's Table 2 exactly
        M, N = 2, 3
        L = M + N

        print(f"Bestgen Table 2 Reproduction: M={M}, N={N}, L={L}")
        print("=" * 60)

        rows = []
        total = 0.0

        for i in range(1, M + 1):
            print(f"\nContributions from {i}-th relevant document:")
            for n in range(i, N + i + 1):
                p_hyper = hypergeom.pmf(i, L, M, n)
                precision = i / n
                final_prob = p_hyper * precision
                contribution = final_prob * precision
                total += contribution

                rows.append(
                    {
                        "i": i,
                        "rank n": n,
                        "P(i in n)": p_hyper,
                        "i/n": precision,
                        "Final prob": final_prob,
                        "Contribution": contribution,
                    }
                )

                print(
                    f"  Rank {n}: P={p_hyper:.4f}, Prec={precision:.4f}, Contrib={contribution:.6f}"
                )

        bestgen_table = pd.DataFrame(rows)
        expected_ap = total / M

        print(f"\nSum of contributions: {total:.6f}")
        print(f"Expected AP = {total:.6f} / {M} = {expected_ap:.6f}")
        print(f"Closed-form verification: {expected_ap_closed_form(M, N):.6f}")
        return bestgen_table

    _()
    return


@app.cell
def _(mo):
    mo.md(
        """
    ## Section 6: Monte Carlo Validation

    Empirical verification through simulation.
    """
    )
    return


@app.cell
def _(average_precision, np):
    def simulate_random_ap(M: int, N: int, trials: int = 10000) -> tuple:
        """Monte Carlo simulation of AP under random ranking."""
        labels = np.array([1] * M + [0] * N)
        aps = []

        rng = np.random.default_rng(42)
        for _ in range(trials):
            rng.shuffle(labels)
            aps.append(average_precision(labels.copy()))

        aps = np.array(aps)
        return aps.mean(), aps.std(), aps

    return (simulate_random_ap,)


@app.cell
def _(expected_ap_closed_form, pd, simulate_random_ap):
    def _():
        # Compare theoretical vs simulated
        simulation_cases = [(5, 15), (10, 40), (20, 80), (50, 450)]

        sim_results = []
        for M, N in simulation_cases:
            theoretical = expected_ap_closed_form(M, N)
            sim_mean, sim_std, _ = simulate_random_ap(M, N, trials=10000)

            sim_results.append(
                {
                    "M": M,
                    "N": N,
                    "L": M + N,
                    "Prevalence": M / (M + N),
                    "Theoretical E[AP]": theoretical,
                    "Simulated E[AP]": sim_mean,
                    "Simulation Std": sim_std,
                    "Error": abs(theoretical - sim_mean),
                }
            )

        simulation_df = pd.DataFrame(sim_results)
        return simulation_df

    _()
    return


@app.cell
def _(mo):
    mo.md(
        """
    ## Section 7: Asymptotic Analysis

    As $L \\to \\infty$ with fixed prevalence $p$:

    $$\\mathbb{E}[\\text{AP}] = p + \\frac{(1-p)\\log L}{L} + O\\left(\\frac{1}{L}\\right)$$

    The correction term vanishes logarithmically.
    """
    )
    return


@app.cell
def _(alt, expected_ap_closed_form, np, pd):
    def _():
        # Demonstrate asymptotic convergence
        prevalence = 0.1
        Ls = np.logspace(1, 4, 50).astype(int)  # L from 10 to 10000

        convergence_data = []
        for L in Ls:
            M = max(1, int(prevalence * L))
            N = L - M
            actual_p = M / L

            expected_ap = expected_ap_closed_form(M, N)

            # Asymptotic approximation using log L
            asymptotic_approx = actual_p + (1 - actual_p) * np.log(L) / L

            convergence_data.append(
                {
                    "L": L,
                    "E[AP]": expected_ap,
                    "Prevalence": actual_p,
                    "Asymptotic": asymptotic_approx,
                    "Error from Prevalence": expected_ap - actual_p,
                    "Relative Error": (expected_ap - actual_p) / actual_p
                    if actual_p > 0
                    else 0,
                }
            )

        convergence_df = pd.DataFrame(convergence_data)

        # Create visualization
        base = alt.Chart(convergence_df).encode(
            x=alt.X(
                "L:Q", scale=alt.Scale(type="log"), title="List Length L (log scale)"
            )
        )

        exact_line = base.mark_line(color="blue").encode(
            y=alt.Y("E[AP]:Q", title="Expected AP"),
            tooltip=["L", "E[AP]", "Prevalence"],
        )

        prevalence_line = base.mark_line(color="red", strokeDash=[5, 5]).encode(
            y="Prevalence:Q", tooltip=["L", "Prevalence"]
        )

        asymptotic_line = base.mark_line(color="green", strokeDash=[3, 3]).encode(
            y="Asymptotic:Q", tooltip=["L", "Asymptotic"]
        )

        convergence_chart = (exact_line + prevalence_line + asymptotic_line).properties(
            width=600,
            height=400,
            title=f"Asymptotic Convergence of E[AP] to Prevalence (p={prevalence})",
        )
        return convergence_chart

    _()
    return


@app.cell
def _(mo):
    mo.md(
        """
    ## Section 8: Statistical Testing Implications

    Using prevalence instead of the exact expected value causes:

    1. **Type I Error Inflation**: False positives when AP > prevalence but < E[AP]
    2. **Power Reduction**: Larger effects needed for significance
    """
    )
    return


@app.cell
def _(alt, expected_ap_closed_form, pd):
    def _():
        # Show the bias impact across different scenarios
        prevalences = [0.05, 0.1, 0.2, 0.5]
        Ls = [50, 100, 200, 500, 1000]

        bias_data = []
        for p_target in prevalences:
            for L in Ls:
                M = max(1, int(p_target * L))
                N = L - M
                actual_p = M / L

                expected_ap = expected_ap_closed_form(M, N)
                bias = expected_ap - actual_p
                relative_bias = bias / actual_p if actual_p > 0 else 0

                bias_data.append(
                    {
                        "Prevalence": p_target,
                        "L": L,
                        "E[AP]": expected_ap,
                        "Naive (p)": actual_p,
                        "Absolute Bias": bias,
                        "Relative Bias (%)": relative_bias * 100,
                    }
                )

        bias_df = pd.DataFrame(bias_data)
        # Altair heatmap
        bias_chart = (
            alt.Chart(bias_df)
            .mark_rect()
            .encode(
                x=alt.X("L:O", title="List Length"),
                y=alt.Y("Prevalence:O", title="Prevalence"),
                color=alt.Color(
                    "Relative Bias (%):Q",
                    scale=alt.Scale(scheme="orangered"),
                    title="Relative Bias (%)",
                ),
                tooltip=[
                    "L",
                    "Prevalence",
                    alt.Tooltip("Relative Bias (%):Q", format=".2f"),
                ],
            )
            .properties(
                width=400, height=300, title="Relative Bias of Naive Approximation"
            )
        )
        return bias_chart

    _()
    return


@app.cell
def _(mo):
    mo.md(
        """
    ## Section 9: Practical Implications Summary

    Key takeaways for practitioners:
    """
    )
    return


@app.cell
def _(expected_ap_closed_form, pd):
    def _():
        # Summary table showing when the correction matters
        practical_cases = [
            ("Small medical dataset", 50, 10),
            ("Medium IR collection", 500, 50),
            ("Large web ranking", 5000, 250),
            ("Massive scale", 50000, 2500),
        ]

        summary_data = []
        for name, L, M in practical_cases:
            N = L - M
            p = M / L
            expected_ap = expected_ap_closed_form(M, N)
            error = expected_ap - p
            rel_error = error / p * 100

            summary_data.append(
                {
                    "Scenario": name,
                    "L": L,
                    "M": M,
                    "Prevalence": f"{p:.1%}",
                    "E[AP] (Exact)": f"{expected_ap:.4f}",
                    "Naive Approx": f"{p:.4f}",
                    "Absolute Error": f"{error:.4f}",
                    "Relative Error": f"{rel_error:.1f}%",
                    "Significant?": "⚠️ Yes" if rel_error > 5 else "No",
                }
            )

        summary_df = pd.DataFrame(summary_data)
        return summary_df

    _()
    return


@app.cell
def _(mo):
    mo.md(
        """
    ## Implementation Guidance

    **When to use each method:**

    1. **Harmonic Formula**: Always preferred for exact calculation (O(L) time)
    2. **Hypergeometric**: Educational purposes or validation (O(ML) time)
    3. **Asymptotic Approximation**: When L > 10⁶ and rough estimate sufficient

    **For statistical testing:**

    - Always use exact expected value, not prevalence
    - The bias is most severe for low prevalence and small L
    - Consider normalized AP for significance testing
    """
    )
    return


@app.cell
def _(expected_ap_closed_form, expected_ap_hypergeometric, pd):
    def _():
        import time

        # Performance comparison
        perf_cases = [(10, 10), (50, 50), (100, 100)]
        perf_results = []

        for M, N in perf_cases:
            L = M + N

            # Time harmonic method
            start = time.perf_counter()
            for _ in range(1000):
                _ = expected_ap_closed_form(M, N)
            harmonic_time = (time.perf_counter() - start) / 1000 * 1000  # ms

            # Time hypergeometric method
            start = time.perf_counter()
            for _ in range(10):
                _ = expected_ap_hypergeometric(M, N)
            hyper_time = (time.perf_counter() - start) / 10 * 1000  # ms

            perf_results.append(
                {
                    "L": L,
                    "Harmonic (ms)": f"{harmonic_time:.3f}",
                    "Hypergeometric (ms)": f"{hyper_time:.3f}",
                    "Speedup": f"{hyper_time / harmonic_time:.0f}x",
                }
            )

        perf_df = pd.DataFrame(perf_results)
        return perf_df

    _()
    return


@app.cell
def _(mo):
    mo.md(
        """
    ## Conclusions

    This notebook demonstrates:

    1. **Exact Formula**: E[AP] = p + O(log L/L), not just p
    2. **Dual Derivation**: Harmonic and hypergeometric methods agree perfectly
    3. **Practical Impact**: Significant bias for small L and low prevalence
    4. **Statistical Testing**: Using naive approximation inflates Type I errors

    The harmonic formula should be used in practice for all finite-sample AP calculations.
    """
    )
    return


if __name__ == "__main__":
    app.run()
