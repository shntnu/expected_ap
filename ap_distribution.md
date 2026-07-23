# Average Precision Under Random Ranking: Exact Expectation and Distribution

**Author:** shntnu and claude

**Date:** December 2024

**MSC Classification:** 62G10, 68T05, 60C05

**Keywords:** Average Precision, Random Ranking, Hypergeometric Distribution, Information Retrieval, Statistical Testing

## Abstract

We derive the exact finite-sample expectation and probability distribution of Average Precision (AP) under uniformly random ranking, correcting the common approximation that equates expected AP with prevalence.
The expectation has a harmonic-number closed form, while the full discrete law is a finite count over relevant-rank subsets, with an equivalent coefficient-generating formula.
Our expectation result shows that $\mathbb{E}[\text{AP}] = p + O(\log L/L)$ where $p$ is the prevalence and $L$ the list length, revealing a persistent positive bias that affects statistical significance testing.

## 1. Introduction

Average Precision (AP) is a fundamental metric in information retrieval, machine learning, and ranking evaluation [Robertson 2008]. It summarizes the precision-recall trade-off into a single scalar and corresponds to the area under the uninterpolated precision-recall curve. Understanding its behavior under the null hypothesis of random ranking is essential for:

1. Statistical significance testing of ranking algorithms
2. Establishing baseline performance expectations
3. Detecting non-random patterns in ranked outputs

While it is commonly assumed that the expected AP under random ranking equals the prevalence (proportion of relevant items), Zhang and Su (2012) derived exact finite-sample moments and Bestgen (2015) later focused specifically on the random-baseline expectation.
For finite samples—particularly common in specialized domains with limited labeled data—the exact expected value differs substantially from prevalence.

### 1.1 Contributions

This paper provides a comprehensive treatment of expected AP under random ranking:

1. **Closed-form Derivation:** We present a complete proof of the exact formula using exchangeability arguments (Theorem 1)
2. **Unified Presentation:** We provide an alternative derivation using harmonic numbers and connect it with Bestgen's (2015) hypergeometric algorithm, showing their equivalence
3. **Asymptotic Analysis:** We characterize the precise $O(\log L/L)$ convergence rate with explicit constants
4. **Full Distribution and Tails:** We give the exact finite PMF, including the multiplicities caused by AP collisions, and an exact recursive tail formula
5. **Practical Implications:** We quantify the impact on statistical testing and provide implementation guidance

## 2. Problem Formulation

### 2.1 Notation and Definitions

Consider a ranking of $L$ items with binary relevance labels $y_1, \ldots, y_L \in \{0,1\}$, where:

- $M$ items are relevant ($\sum_{i=1}^L y_i = M$)
- $N = L - M$ items are non-relevant
- $p = M/L$ denotes the prevalence

**Definition 1 (Average Precision).** The Average Precision of a ranking is:

$$\text{AP} = \frac{1}{M} \sum_{k=1}^{L} \text{Prec}@k \cdot y_k = \frac{1}{M} \sum_{k: y_k=1} \text{Prec}@k$$

where $\text{Prec}@k = \frac{1}{k}\sum_{j=1}^{k} y_j$ is the precision at rank $k$.

**Definition 2 (Random Ranking).** A uniformly random ranking is a permutation of the $L$ items chosen uniformly from all $L!$ possible permutations.

### 2.2 The Approximation Gap

The naive approximation $\mathbb{E}[\text{AP}] \approx p$ assumes that under random ranking, relevant items are uniformly distributed, leading to a constant precision-recall curve at height $p$. However, this ignores the discrete nature of finite samples and the dependency structure in the precision calculations.

## 3. Main Results

### 3.1 Exact Expected Value

**Theorem 1 (Closed-form Expected AP).** *Under uniformly random ranking of $L = M + N$ items with $M$ relevant items, the expected Average Precision is:*

$$\mathbb{E}[\text{AP}] = \frac{1}{L}\left[\frac{M-1}{L-1}(L-H_L) + H_L\right]$$

*where $H_L = \sum_{k=1}^{L} \frac{1}{k}$ is the $L$-th harmonic number.*

**Proof.** We exploit the exchangeability of items under random ranking. Consider a uniformly chosen relevant item at rank $R$, where $P(R = r) = \frac{1}{L}$ for $r \in \{1, \ldots, L\}$.

Given $R = r$, let $X$ denote the number of other relevant items among the first $r-1$ positions. By the hypergeometric distribution:

$$X \mid R = r \sim \text{Hypergeometric}(L-1, M-1, r-1)$$

with $\mathbb{E}[X \mid R = r] = \frac{(r-1)(M-1)}{L-1}$.

The precision at rank $r$ is:
$$\text{Prec}@r = \frac{X+1}{r}$$

Therefore:
$$\mathbb{E}[\text{Prec}@r \mid R = r] = \frac{1}{r}\left(\frac{(r-1)(M-1)}{L-1} + 1\right) = \frac{(r-1)(M-1)}{(L-1)r} + \frac{1}{r}$$

By the exchangeability argument, each relevant item contributes equally to the expected AP, so:

$$\mathbb{E}[\text{AP}] = \mathbb{E}[\text{Prec}@R] = \frac{1}{L}\sum_{r=1}^{L}\left(\frac{(r-1)(M-1)}{(L-1)r} + \frac{1}{r}\right)$$

Using the identities:

- $\sum_{r=1}^{L}\frac{r-1}{r} = \sum_{r=1}^{L}(1 - \frac{1}{r}) = L - H_L$
- $\sum_{r=1}^{L}\frac{1}{r} = H_L$

We obtain:
$$\mathbb{E}[\text{AP}] = \frac{1}{L}\left[\frac{M-1}{L-1}(L-H_L) + H_L\right] \quad \square$$

### 3.2 Alternative Forms

**Corollary 1 (Prevalence-plus-correction form).** *The expected AP can be expressed as:*

$$\mathbb{E}[\text{AP}] = p + \frac{N(H_L - 1)}{L(L-1)}$$

*where the second term represents the finite-sample correction.*

**Proof.** Algebraic manipulation of Theorem 1 yields:
$$\mathbb{E}[\text{AP}] = \frac{M}{L} + \frac{N}{L(L-1)}(H_L - 1) = p + (1-p)\frac{H_L - 1}{L-1} \quad \square$$

### 3.3 Algorithmic Derivation

**Theorem 2 (Bestgen 2015).** *The expected AP can be computed algorithmically as:*

$$\mathbb{E}[\text{AP}] = \frac{1}{M} \sum_{i=1}^{M} \sum_{n=i}^{N+i} P_{\text{hyper}}(i; L, M, n) \cdot \left(\frac{i}{n}\right)^2$$

*where $P_{\text{hyper}}(i; L, M, n)$ is the hypergeometric probability mass function.*

**Proof Sketch.** For each $i$-th relevant item:

1. It can appear at ranks $n \in \{i, i+1, \ldots, N+i\}$
2. The probability of exactly $i$ successes in the first $n$ draws is hypergeometric
3. Given $i$ successes in $n$ draws, the probability the $i$-th occurs at position $n$ is $i/n$
4. The precision at rank $n$ with $i$ relevant items is $i/n$

The double summation aggregates these contributions. $\square$

**Remark.** Bestgen's algorithmic approach, while computationally more intensive ($O(ML)$ operations), provides insight into the probabilistic structure and serves as independent validation of Theorem 1. We include it here to demonstrate the equivalence of the two methods.

### 3.4 Exact AP Distribution

Let $1 \le R_1 < \cdots < R_M \le L$ be the ordered ranks of the relevant items.
A uniform item permutation induces a uniform choice among the $\binom{L}{M}$ possible relevant-rank sets: every set has exactly $M!(L-M)!$ permutation preimages.
At rank $R_j$, exactly $j$ relevant items have appeared, so

$$A = \text{AP} = \frac{1}{M}\sum_{j=1}^{M}\frac{j}{R_j}.$$

**Theorem 3 (Exact AP PMF).** *For $1 \le M \le L$ and any rational $a$,*

$$
\Pr(A=a)
= \frac{1}{\binom{L}{M}}
\sum_{1 \le r_1 < \cdots < r_M \le L}
\mathbf{1}\left\{a=\frac{1}{M}\sum_{j=1}^{M}\frac{j}{r_j}\right\}.
$$

Equivalently, the AP law is the finite mixture

$$
\mathcal{L}(A)
= \frac{1}{\binom{L}{M}}
\sum_{1 \le r_1 < \cdots < r_M \le L}
\delta_{\frac{1}{M}\sum_{j=1}^{M}j/r_j}.
$$

This formula retains multiplicity because the map from rank sets to AP values is not injective.
For example, when $L=6$ and $M=2$, rank sets $(2,6)$ and $(3,4)$ both give $A=5/12$, so $\Pr(A=5/12)=2/15$.

A coefficient form makes the same multiplicities explicit.
Let $D=L!$, define

$$K(r_1,\ldots,r_M)=\sum_{j=1}^{M}j\frac{D}{r_j},$$

and let

$$P_{L,M}(z)=\sum_{1 \le r_1 < \cdots < r_M \le L}z^{K(r_1,\ldots,r_M)}.$$

Then every AP value lies on the rational grid $k/(MD)$ and

$$
\Pr\left(A=\frac{k}{MD}\right)
=\frac{[z^k]P_{L,M}(z)}{\binom{L}{M}},
\qquad
P_{L,M}(1)=\binom{L}{M}.
$$

For $M=0$, the repository's convention gives the point mass $A=0$.
For $M=L$, the law is the point mass $A=1$.
The Lean theorem `uniformAPMass_closed_form_explicit` proves the subset-count formula directly from the original uniform-permutation definition.

### 3.5 Exact Tail Reduction

Let

$$T_{L,M}(t)=\Pr(A_{L,M}\ge t).$$

Condition on the final relevant rank $R_M=k$.
Its distribution is

$$
\Pr(R_M=k)=\frac{\binom{k-1}{M-1}}{\binom{L}{M}},
$$

and the preceding $M-1$ ranks form a uniform $(M-1)$-subset of $\{1,\ldots,k-1\}$.
Moreover,

$$
A_{L,M}=\frac{M-1}{M}A_{k-1,M-1}+\frac1k.
$$

**Theorem 4 (Exact AP Tail Recurrence).** *For $M>1$,*

$$
T_{L,M}(t)
=\frac1{\binom{L}{M}}
\sum_{k=M}^{L}\binom{k-1}{M-1}
T_{k-1,M-1}\left(\frac{M}{M-1}\left(t-\frac1k\right)\right).
$$

*Proof.* Condition on $R_M=k$ using the preceding two identities and sum over $k=M,\ldots,L$. $\square$

The base case is elementary:

$$
T_{L,1}(t)=
\begin{cases}
1, & t\le0,\\
\min(L,\lfloor1/t\rfloor)/L, & 0<t\le1,\\
0, & t>1.
\end{cases}
$$

The other nearly deterministic edge has a harmonic description.
When $L\ge2$ and $M=L-1$, let $K$ be the rank of the sole nonrelevant item.
Then $K$ is uniform on $\{1,\ldots,L\}$ and

$$
A_K=1-\frac{H_L-H_K}{L-1}.
$$

Consequently,

$$
T_{L,L-1}(t)
=\frac1L\#\left\{K:H_K\ge H_L-(L-1)(1-t)\right\}.
$$

This uses harmonic numbers, but evaluating it still requires finding the first harmonic number above the threshold.

There is also an elementary exact formula for the extreme upper tail.
Let $N=L-M$, assume $M\ge2$, and define

$$
b_{L,M}=1-\frac{2M+1}{M^2(M+1)}.
$$

For every threshold $b_{L,M}<t\le1$,

$$
T_{L,M}(t)
=
\frac{
1+\min\left(
N,
\left\lfloor
\frac{M^2(1-t)}{1-M(1-t)}
\right\rfloor
\right)
}{\binom LM}.
$$

To see this, write each relevant rank as $R_j=j+d_j$, where

$$
0\le d_1\le\cdots\le d_M\le N.
$$

The loss from perfect AP is

$$
1-A=\frac1M\sum_{j=1}^M\frac{d_j}{j+d_j}.
$$

If any of the first $M-1$ displacements is positive, the smallest possible loss occurs at $(d_1,\ldots,d_M)=(0,\ldots,0,1,1)$ and equals $(2M+1)/(M^2(M+1))$.
Above $b_{L,M}$, every qualifying rank set therefore has the form $(0,\ldots,0,d)$.
For that set, $A=1-d/(M(M+d))$, and solving $A\ge t$ gives

$$
0\le d\le
\min\left(
N,
\left\lfloor\frac{M^2(1-t)}{1-M(1-t)}\right\rfloor
\right).
$$

The lower endpoint of this interval is intentionally strict when $N\ge1$.
At $t=b_{L,M}$, the displacement pattern $(0,\ldots,0,1,1)$ also enters the tail, so the displayed numerator undercounts by one.
When $N=0$, AP is identically one and the formula remains valid at the endpoint.

An elementary formula also holds near the minimum AP.
Assume $M\ge2$ and $N\ge1$, and set

$$
a_{L,M}=1-\frac{N}{M}(H_L-H_N),
\qquad
c_{L,M}=a_{L,M}+\frac{3N+2}{MN(N+1)(N+2)}.
$$

For every $a_{L,M}\le t\le c_{L,M}$,

$$
T_{L,M}(t)
=1-\frac{1}{\binom LM}
\min\left(
N+1,
\left\lceil
\frac{M(N+1)^2(t-a_{L,M})}
{1+M(N+1)(t-a_{L,M})}
\right\rceil
\right).
$$

For the proof, retain the displacements $d_j=R_j-j$ and put $e_j=N-d_j$.
Then $N\ge e_1\ge\cdots\ge e_M\ge0$, the minimum AP occurs at $e=(0,\ldots,0)$, and

$$
A-a_{L,M}
=\frac1M\sum_{j=1}^M
\frac{j e_j}{(N+j-e_j)(N+j)}.
$$

Outside the family $e=(d,0,\ldots,0)$, the smallest increase is attained at $e=(1,1,0,\ldots,0)$ and equals $(3N+2)/(MN(N+1)(N+2))$.
Thus, throughout the displayed interval, the rank sets excluded from the upper tail all belong to the one-parameter family.
For that family,

$$
A-a_{L,M}=\frac{d}{M(N+1-d)(N+1)}.
$$

Solving the strict inequality $A<t$ and counting the integers $0\le d\le N$ gives the ceiling term above.
Unlike the near-one formula, this band includes its upper endpoint because the new configuration at $c_{L,M}$ satisfies $A=t$ and remains in the upper tail.

The recurrence above computes an exact tail directly, but unrolling it reproduces the nested rank-set calculation rather than a harmonic-number collapse.
The obstruction is visible already for $M=2$.
For a rational threshold $t=p/q>0$ in lowest terms, define, for $1\le r<L$,

$$
U_r=
\begin{cases}
L, & 2pr\le q,\\
\min\left(L,\left\lfloor\dfrac{2qr}{2pr-q}\right\rfloor\right), & 2pr>q.
\end{cases}
$$

Solving the tail inequality for the second rank gives the exact one-dimensional formula

$$
T_{L,2}(p/q)
=\frac1{\binom L2}\sum_{r=1}^{L-1}\max(0,U_r-r).
$$

Equivalently, a rank pair $(r,s)$ belongs to the tail exactly when

$$
(2pr-q)(ps-q)\le q^2.
$$

At equality this becomes a divisor equation; for example, every atom can be recovered from factor pairs of $q^2$ subject to the rank and congruence constraints.
For $t=1/(2n)$, the tail boundary is the shifted hyperbola

$$
(r-n)(s-2n)\le2n^2.
$$

The divisor sum occurs verbatim in this family.
For every integer $n\ge1$ and $L\ge2n^2+2n$,

$$
\binom L2 T_{L,2}\left(\frac1{2n}\right)
=nL-\frac{n(n+1)}2
+\sum_{d=1}^{2n-1}\left\lfloor\frac{2n^2}{d}\right\rfloor.
$$

Indeed, ranks $r\le n$ contribute $\sum_{r=1}^n(L-r)$.
Writing every remaining contributing rank as $r=n+d$ leaves $1\le d\le2n-1$ and contribution $n-d+\lfloor2n^2/d\rfloor$; the linear terms cancel after summation.
Thus even the two-relevant-item tail contains a standard truncated divisor-summatory function, or equivalently a bounded hyperbola lattice-point count.
The connection is exact.
Write $q=mp+c$ with $0\le c<p$ and set $n=2pr-q$ in the nontrivial part of the sum.
Then

$$
\left\lfloor\frac{2qr}{2pr-q}\right\rfloor
=m+\left\lfloor\frac{\lfloor q^2/n\rfloor+c}{p}\right\rfloor.
$$

When $p=1$ and $q$ is even, $n=2d$ and the varying term is $\lfloor(q^2/2)/d\rfloor$, an interval of the ordinary divisor summatory floor sum.
The usual reciprocity for linear floor sums does not remove this hyperbolic arithmetic term.
Known exact algorithms for the ordinary divisor summatory function likewise evaluate the underlying lattice-point count rather than replace it by a harmonic or elementary expression [7].
This explains why the expectation can simplify through linearity while the exact tail retains discrete arithmetic structure.

The support can also be combinatorially large.
Let $\mathcal P$ contain $K$ primes satisfying $M<p\le L$.
AP is injective on the $M$-subsets of $\mathcal P$: if two such subsets had equal AP, multiplying by the product of their union and reducing modulo each prime would force that prime to occur with the same positional coefficient on both sides.
Because every positional coefficient is at most $M<p$, congruence implies equality of the positions and hence equality of the subsets.
Consequently,

$$
|\operatorname{supp}(A)|\ge\binom KM.
$$

For example, the 21 primes in $(10,100]$ imply at least $\binom{21}{10}=352716$ distinct AP values when $L=100$ and $M=10$.
Any exact tail formula for arbitrary $t$ must encode these breakpoints, whether through cases, floors, recurrence states, or coefficient extraction.
This rules out a short explicit atom table, but it is not a symbolic formula-size lower bound or a proof of computational hardness.

## 4. Asymptotic Analysis

### 4.1 Convergence Rate

**Theorem 5 (Asymptotic Behavior).** *As $L \to \infty$ with prevalence $p$ held fixed:*

$$\mathbb{E}[\text{AP}] = p + \frac{(1-p)\log L}{L} + O\left(\frac{1}{L}\right)$$

**Proof.** Using the well-known asymptotic expansion of the harmonic number [see, e.g., Graham et al. 1994], $H_L = \log L + \gamma + \frac{1}{2L} + O(L^{-2})$ where $\gamma \approx 0.5772$ is the Euler-Mascheroni constant:

$$\mathbb{E}[\text{AP}] - p = \frac{N(H_L - 1)}{L(L-1)} = \frac{(1-p)(\log L + \gamma - 1)}{L-1} + O(L^{-2})$$

The dominant term is $\frac{(1-p)\log L}{L}$. $\square$

### 4.2 Practical Implications

**Corollary 2.** *The relative error $(\mathbb{E}[\text{AP}] - p)/p$ is:*

$$\frac{\mathbb{E}[\text{AP}] - p}{p} = \frac{1-p}{p} \cdot \frac{H_L - 1}{L-1} \approx \frac{1-p}{p} \cdot \frac{\log L}{L}$$

This shows the bias is most pronounced when:

1. Prevalence is low (small $p$)
2. Sample size is small (small $L$)

**Example.** For $p = 0.1$:

- $L = 100$: relative error ≈ 38%
- $L = 1000$: relative error ≈ 6%
- $L = 10000$: relative error ≈ 0.8%

## 5. Statistical Testing Implications

### 5.1 Hypothesis Testing

For testing whether an observed AP differs significantly from random:

**Null Hypothesis:** $H_0$: Ranking is uniformly random
**Test Statistic:** Observed AP

Under $H_0$, the expected value is **not** the prevalence but rather given by Theorem 1. Using the incorrect null expectation (prevalence) leads to:

1. **Type I Error Inflation:** Falsely rejecting $H_0$ when AP exceeds prevalence but not $\mathbb{E}[\text{AP}]$
2. **Power Reduction:** Requiring larger effect sizes to achieve significance

### 5.2 Exact Variance and Tail Probabilities

The full PMF in Theorem 3 already determines the exact finite-sample variance:

$$
\operatorname{Var}(A)
= \sum_{a} a^2\Pr(A=a)-\mathbb{E}[A]^2.
$$

It also gives exact upper-tail probabilities for an observed value $a_{\mathrm{obs}}$:

$$
\Pr(A \ge a_{\mathrm{obs}})
= \sum_{a \ge a_{\mathrm{obs}}}\Pr(A=a).
$$

The recurrence in Section 3.5 computes one exact tail without first constructing the whole PMF.
Its worst-case work remains combinatorial, as the $M=2$ divisor-style reduction already indicates.
The variance now has a compact analytic expression comparable to Theorem 1, proved in Lean (`varianceAP_closed_form` in `lean/ap_moments.lean`), recorded with its full status in `AP_MOMENTS.md`, and implemented in `ap_moments.py`; the third moment likewise has an exact closed form (`eap3`, numerically verified, requiring one generator beyond the harmonic basis).
The remaining problem is to compute tail probabilities scalably without hiding the same count in coefficient extraction or nested floor sums.

## 6. Implementation Notes

### 6.1 Computational Considerations

1. **Harmonic Numbers:** For $L \leq 10^6$, direct summation is efficient
2. **For larger $L$:** Use approximation $H_L \approx \log L + \gamma + \frac{1}{2L}$
3. **Hypergeometric Method:** Suitable for validation but computationally intensive for large $L$

### 6.2 Code Availability

Python implementations accompany this paper in the same repository: `expected_ap.py` (expectation methods), `ap_distribution.py` (exact PMF and CDF explorer), and `ap_moments.py` (variance, covariance, and mAP null).

## 7. Related Work

- **Robertson (2008):** Introduced alternative AP formulations but assumed asymptotic behavior
- **Zhang and Su (2012):** Derived exact hit-rank marginals and pairwise joint laws, used them for exact first and second moments, and proposed a normal approximation
- **Lopes and Bontempi (2014):** Derived exact AP-style AUPRC moments and proposed a moment-matched beta approximation to the discrete null distribution
- **Bestgen (2015):** Provided an exact hypergeometric algorithm focused on the random-baseline expectation
- **Yilmaz et al. (2008):** Studied AP variance but under different assumptions

## 8. Conclusion

We have provided exact finite-sample formulas for both the expectation and full discrete distribution of Average Precision under random ranking.
The harmonic expectation reveals the bias in the prevalence approximation, while the rank-subset PMF gives exact atom and tail probabilities.

### Future Directions

The compact second-moment and variance formula, formerly listed here, is delivered in `AP_MOMENTS.md` and proved in Lean; the exact third moment is delivered there as well (verified, not yet formalised).
The second item below concerns computational scale, not the existence of exact finite answers.

1. Extend the analysis to graded-relevance metrics such as NDCG and ERR
2. Develop scalable exact algorithms or controlled approximations for tail probabilities at large $L$ and $M$

## References

[1] Bestgen, Y. (2015). Exact Expected Average Precision of the Random Baseline for System Evaluation. *Prague Bulletin of Mathematical Linguistics*, 103, 131-138.

[2] Graham, R. L., Knuth, D. E., & Patashnik, O. (1994). *Concrete Mathematics: A Foundation for Computer Science* (2nd ed.). Addison-Wesley.

[3] Robertson, S. (2008). A new interpretation of average precision. *Proceedings of SIGIR*, 689-690.

[4] Yilmaz, E., Aslam, J. A., & Robertson, S. (2008). A new rank correlation coefficient for information retrieval. *Proceedings of SIGIR*, 587-594.

[5] Zhang, P., & Su, W. (2012). Statistical inference on recall, precision and average precision under random selection. *Proceedings of FSKD*, 1348-1352.

[6] Lopes, M., & Bontempi, G. (2014). On the null distribution of the precision and recall curve. *ECML PKDD*, 322-337.

[7] Sladkey, R. (2012). A successive approximation algorithm for computing the divisor summatory function. *arXiv:1206.3369*.

## Appendix A: Proof of Harmonic Identity

**Lemma A.1.** $\sum_{r=1}^{L}\frac{r-1}{r} = L - H_L$

**Proof.**
$$\sum_{r=1}^{L}\frac{r-1}{r} = \sum_{r=1}^{L}\left(1 - \frac{1}{r}\right) = L - \sum_{r=1}^{L}\frac{1}{r} = L - H_L \quad \square$$

## Appendix B: Numerical Validation

We validate our formulas through three independent methods:

1. **Closed-form formula** (Theorem 1): Direct calculation using harmonic numbers
2. **Hypergeometric algorithm** (Theorem 2): Iterative computation following Bestgen (2015)
3. **Monte Carlo simulation**: Empirical estimation via random permutations

All three methods agree to machine precision for the exact methods (difference < $10^{-15}$) and to sampling error for Monte Carlo (< $10^{-4}$ with 10,000 trials). We tested configurations ranging from $L = 5$ to $L = 50,000$ with various prevalence levels.

The accompanying interactive notebook (`expected_ap.py`) provides:

- Complete numerical comparisons across all test cases
- Reproduction of Bestgen's Table 2
- Performance benchmarks comparing computational efficiency
- Visualization of convergence behavior

These empirical results confirm both the theoretical equivalence of the harmonic and hypergeometric approaches and the practical accuracy of the closed-form formula.
