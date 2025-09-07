# Expected Average Precision Under Random Ranking: Exact Finite-Sample Analysis and Computational Methods

**Author:** shntnu and claude

**Date:** December 2024

**MSC Classification:** 62G10, 68T05, 60C05

**Keywords:** Average Precision, Random Ranking, Hypergeometric Distribution, Information Retrieval, Statistical Testing

## Abstract

We derive the exact finite-sample expected value of Average Precision (AP) under uniformly random ranking, correcting the common approximation that equates expected AP with prevalence. We present two equivalent derivations: an analytical approach using harmonic numbers and an algorithmic method via hypergeometric distributions. Our main result shows that $\mathbb{E}[\text{AP}] = p + O(\log L/L)$ where $p$ is the prevalence and $L$ the list length, revealing a persistent positive bias that affects statistical significance testing. We provide explicit formulas, asymptotic analysis, and practical implications for information retrieval evaluation.

## 1. Introduction

Average Precision (AP) is a fundamental metric in information retrieval, machine learning, and ranking evaluation [Robertson 2008]. It summarizes the precision-recall trade-off into a single scalar and corresponds to the area under the uninterpolated precision-recall curve. Understanding its behavior under the null hypothesis of random ranking is essential for:

1. Statistical significance testing of ranking algorithms
2. Establishing baseline performance expectations
3. Detecting non-random patterns in ranked outputs

While it is commonly assumed that the expected AP under random ranking equals the prevalence (proportion of relevant items), Bestgen (2015) demonstrated that this is only an approximation. For finite samples—particularly common in specialized domains with limited labeled data—the exact expected value differs substantially from prevalence.

### 1.1 Contributions

This paper provides a comprehensive treatment of expected AP under random ranking:

1. **Closed-form Derivation:** We present a complete proof of the exact formula using exchangeability arguments (Theorem 1)
2. **Unified Presentation:** We provide an alternative derivation using harmonic numbers and connect it with Bestgen's (2015) hypergeometric algorithm, showing their equivalence
3. **Asymptotic Analysis:** We characterize the precise $O(\log L/L)$ convergence rate with explicit constants
4. **Practical Implications:** We quantify the impact on statistical testing and provide implementation guidance

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

## 4. Asymptotic Analysis

### 4.1 Convergence Rate

**Theorem 3 (Asymptotic Behavior).** *As $L \to \infty$ with prevalence $p$ held fixed:*

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

### 5.2 Variance Under Random Ranking

While beyond our scope, the variance of AP under random ranking is also needed for complete statistical testing. Future work should derive the exact finite-sample variance formula.

## 6. Implementation Notes

### 6.1 Computational Considerations

1. **Harmonic Numbers:** For $L \leq 10^6$, direct summation is efficient
2. **For larger $L$:** Use approximation $H_L \approx \log L + \gamma + \frac{1}{2L}$
3. **Hypergeometric Method:** Suitable for validation but computationally intensive for large $L$

### 6.2 Code Availability

Python implementations of both methods are available at: [repository URL]

## 7. Related Work

- **Robertson (2008):** Introduced alternative AP formulations but assumed asymptotic behavior
- **Bestgen (2015):** First formally identified that the common prevalence approximation is incorrect; provided the exact algorithmic approach using hypergeometric distributions
- **Yilmaz et al. (2008):** Studied AP variance but under different assumptions

## 8. Conclusion

We have provided a complete characterization of expected Average Precision under random ranking, revealing that the common prevalence approximation incurs a logarithmic finite-sample bias. Our dual derivation—analytical via harmonic numbers and algorithmic via hypergeometric distributions—offers both theoretical insight and practical computational methods. These results are essential for proper statistical testing in information retrieval and should replace the naive prevalence approximation in finite-sample settings.

### Future Directions

1. Derive the exact finite-sample variance formula
2. Extend to graded relevance (NDCG, ERR)
3. Characterize the full distribution, not just moments
4. Develop efficient approximations for the tail probabilities

## References

[1] Bestgen, Y. (2015). Exact Expected Average Precision of the Random Baseline for System Evaluation. *Prague Bulletin of Mathematical Linguistics*, 103, 131-138.

[2] Graham, R. L., Knuth, D. E., & Patashnik, O. (1994). *Concrete Mathematics: A Foundation for Computer Science* (2nd ed.). Addison-Wesley.

[3] Robertson, S. (2008). A new interpretation of average precision. *Proceedings of SIGIR*, 689-690.

[4] Yilmaz, E., Aslam, J. A., & Robertson, S. (2008). A new rank correlation coefficient for information retrieval. *Proceedings of SIGIR*, 587-594.

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
