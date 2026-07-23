# /// script
# requires-python = ">=3.12"
# dependencies = [
#     "altair==5.5.0",
#     "marimo",
# ]
# ///

import marimo

__generated_with = "0.23.14"
app = marimo.App(width="medium")


@app.cell
def _():
    from collections import Counter
    from fractions import Fraction
    from itertools import combinations
    from math import comb

    import altair as alt
    import marimo as mo

    return Counter, Fraction, alt, comb, combinations, mo


@app.cell
def _(mo):
    mo.md(r"""
    # Exact Average Precision Distribution Under Random Ranking

    If the relevant ranks are $1 \le R_1 < \cdots < R_M \le L$, then

    $$
    \operatorname{AP}=\frac{1}{M}\sum_{j=1}^{M}\frac{j}{R_j}.
    $$

    Every $M$-subset of ranks is equally likely, so an AP atom's probability is its
    number of rank-set preimages divided by $\binom{L}{M}$.
    """)
    return


@app.cell
def _(Counter, Fraction, combinations):
    def average_precision_from_ranks(ranks: tuple[int, ...]) -> Fraction:
        if not ranks:
            return Fraction(0)
        return sum(
            (Fraction(index, rank) for index, rank in enumerate(ranks, start=1)),
            Fraction(0),
        ) / len(ranks)

    def ap_distribution_counts(list_length: int, relevant_count: int) -> Counter:
        if not 0 <= relevant_count <= list_length:
            raise ValueError("Require 0 <= M <= L")
        if relevant_count == 0:
            return Counter({Fraction(0): 1})
        return Counter(
            average_precision_from_ranks(ranks)
            for ranks in combinations(range(1, list_length + 1), relevant_count)
        )

    def expected_ap_exact(list_length: int, relevant_count: int) -> Fraction:
        if not 0 <= relevant_count <= list_length or list_length == 0:
            raise ValueError("Require 0 <= M <= L and L > 0")
        if relevant_count == 0:
            return Fraction(0)
        if list_length == 1:
            return Fraction(1)
        harmonic = sum(
            (Fraction(1, rank) for rank in range(1, list_length + 1)),
            Fraction(0),
        )
        return Fraction(1, list_length) * (
            Fraction(relevant_count - 1, list_length - 1) * (list_length - harmonic)
            + harmonic
        )

    return ap_distribution_counts, expected_ap_exact


@app.cell
def _(mo):
    # ponytail: exhaustive enumeration is capped at L=14; use the rank-inclusion
    # recurrence if larger exact distributions become necessary.
    list_length = mo.ui.slider(
        start=1,
        stop=14,
        step=1,
        value=6,
        show_value=True,
        label="Total items (L)",
    )
    return (list_length,)


@app.cell
def _(list_length, mo):
    relevant_count = mo.ui.slider(
        start=0,
        stop=list_length.value,
        step=1,
        value=min(2, list_length.value),
        show_value=True,
        label="Relevant items (M)",
    )
    return (relevant_count,)


@app.cell
def _(list_length, mo, relevant_count):
    mo.hstack([list_length, relevant_count], justify="start", gap=2)
    return


@app.cell
def _(
    Fraction,
    ap_distribution_counts,
    comb,
    expected_ap_exact,
    list_length,
    relevant_count,
):
    selected_L = int(list_length.value)
    selected_M = int(relevant_count.value)
    ap_counts = ap_distribution_counts(selected_L, selected_M)
    ranking_count = comb(selected_L, selected_M)

    cumulative_count = 0
    pmf_records = []
    for ap_value, multiplicity in sorted(ap_counts.items()):
        cumulative_count += multiplicity
        probability = Fraction(multiplicity, ranking_count)
        pmf_records.append(
            {
                "ap": float(ap_value),
                "ap_exact": str(ap_value),
                "count": multiplicity,
                "probability": float(probability),
                "probability_exact": str(probability),
                "cdf": cumulative_count / ranking_count,
            }
        )

    distribution_mean = (
        sum(
            (ap_value * count for ap_value, count in ap_counts.items()),
            Fraction(0),
        )
        / ranking_count
    )
    closed_form_mean = expected_ap_exact(selected_L, selected_M)
    collision_count = sum(count > 1 for count in ap_counts.values())
    largest_multiplicity = max(ap_counts.values())
    return (
        closed_form_mean,
        collision_count,
        distribution_mean,
        largest_multiplicity,
        pmf_records,
        ranking_count,
        selected_L,
        selected_M,
    )


@app.cell
def _(
    closed_form_mean,
    collision_count,
    distribution_mean,
    largest_multiplicity,
    mo,
    pmf_records,
    ranking_count,
    selected_L,
    selected_M,
):
    mo.md(
        f"""
    ## Exact result for L={selected_L}, M={selected_M}

    - Rank sets: **{ranking_count:,}**
    - Distinct AP atoms: **{len(pmf_records):,}**
    - Atoms with collisions: **{collision_count:,}**
    - Largest multiplicity: **{largest_multiplicity:,}**
    - Mean from the PMF: **{distribution_mean}** ({float(distribution_mean):.8f})
    - Harmonic closed-form mean: **{closed_form_mean}** ({float(closed_form_mean):.8f})
    """
    )
    return


@app.cell
def _(alt, pmf_records):
    chart_data = alt.Data(values=pmf_records)
    pmf_chart = (
        alt.Chart(chart_data)
        .mark_bar(color="#3B82F6")
        .encode(
            x=alt.X("ap:Q", title="Average Precision", scale=alt.Scale(domain=[0, 1])),
            y=alt.Y("probability:Q", title="Probability"),
            tooltip=[
                alt.Tooltip("ap_exact:N", title="AP"),
                alt.Tooltip("count:Q", title="Rank sets"),
                alt.Tooltip("probability_exact:N", title="Probability"),
            ],
        )
        .properties(height=240, title="Probability mass function")
    )
    cdf_chart = (
        alt.Chart(chart_data)
        .mark_line(point=True, color="#0F766E")
        .encode(
            x=alt.X("ap:Q", title="Average Precision", scale=alt.Scale(domain=[0, 1])),
            y=alt.Y(
                "cdf:Q", title="Cumulative probability", scale=alt.Scale(domain=[0, 1])
            ),
            tooltip=[
                alt.Tooltip("ap_exact:N", title="AP"),
                alt.Tooltip("cdf:Q", title="CDF", format=".6f"),
            ],
        )
        .properties(height=240, title="Cumulative distribution function")
    )
    distribution_chart = alt.vconcat(pmf_chart, cdf_chart).resolve_scale(x="shared")
    distribution_chart
    return


@app.cell
def _(mo, pmf_records):
    mo.vstack(
        [
            mo.md("## Exact atoms"),
            mo.ui.table(
                pmf_records,
                pagination=True,
                page_size=10,
                selection=None,
                label="Exact AP probability mass function",
            ),
        ]
    )
    return


@app.cell
def _(Fraction, ap_distribution_counts, comb, expected_ap_exact):
    for check_L in range(1, 10):
        for check_M in range(check_L + 1):
            check_counts = ap_distribution_counts(check_L, check_M)
            check_total = comb(check_L, check_M)
            assert sum(check_counts.values()) == check_total
            check_mean = (
                sum(
                    (value * count for value, count in check_counts.items()),
                    Fraction(0),
                )
                / check_total
            )
            assert check_mean == expected_ap_exact(check_L, check_M)

    assert ap_distribution_counts(6, 2)[Fraction(5, 12)] == 2
    return


@app.cell
def _(mo):
    mo.md(r"""
    ## What the plots count

    The PMF is

    $$
    \Pr(\operatorname{AP}=a)
    =\frac{\#\left\{1\le r_1<\cdots<r_M\le L:
    \frac{1}{M}\sum_{j=1}^{M}\frac{j}{r_j}=a\right\}}
    {\binom{L}{M}}.
    $$

    Multiplicities matter. For $L=6, M=2$, rank sets $(2,6)$ and $(3,4)$
    both produce $\operatorname{AP}=5/12$, giving that atom probability $2/15$.
    """)
    return


if __name__ == "__main__":
    app.run()
