# Expected Average Precision Under Random Ranking: A Finite-Sample Analysis

## Abstract

We derive the exact finite-sample expected value of Average Precision (AP) under uniformly random ranking. We show that the expected AP equals the prevalence plus a positive bias term of order $O(\log L/L)$, providing precise characterization of the null distribution for statistical testing in information retrieval.

## 1. Introduction

Average Precision (AP) is a fundamental metric in information retrieval and ranking evaluation. Understanding its behavior under the null hypothesis of random ranking is essential for statistical significance testing. We present a rigorous derivation of the expected AP for finite samples with $M$ relevant items among $L$ total items.

## 2. Problem Formulation

Consider a ranking of $L$ items with binary relevance labels $y_1, \ldots, y_L \in \{0,1\}$, where exactly $M$ items are relevant ($y_i = 1$). The Average Precision is defined as:

$$\text{AP} = \frac{1}{M} \sum_{k=1}^{L} \text{Prec}@k \cdot y_k$$

where $\text{Prec}@k = \frac{1}{k}\sum_{j=1}^{k} y_j$ denotes the precision at rank $k$.

## 3. Main Result

**Theorem 1.** *Under uniformly random ranking of $L = M + N$ items with $M$ relevant items, the expected Average Precision is:*

$$\mathbb{E}[\text{AP}] = \frac{1}{L}\left[\frac{M-1}{L-1}(L-H_L) + H_L\right]$$

*where $H_L = \sum_{k=1}^{L} \frac{1}{k}$ is the $L$-th harmonic number.*

**Proof.** By exchangeability of the ranking, we reduce the problem to analyzing a single randomly chosen relevant item. Let $R$ denote the rank of a uniformly chosen relevant item. Under random ranking, $P(R = r) = \frac{1}{L}$ for $r = 1, \ldots, L$.

Given $R = r$, let $X$ denote the number of other relevant items among ranks $1, \ldots, r-1$. Then $X$ follows a hypergeometric distribution:

$$X \mid R = r \sim \text{Hypergeometric}(L-1, M-1, r-1)$$

with expectation:

$$\mathbb{E}[X \mid R = r] = \frac{(r-1)(M-1)}{L-1}$$

The precision at rank $r$ is $\text{Prec}@r = \frac{X+1}{r}$, yielding:

$$\mathbb{E}[\text{Prec}@r \mid R = r] = \frac{(r-1)(M-1)}{(L-1)r} + \frac{1}{r}$$

By symmetry across all relevant items, $\mathbb{E}[\text{AP}] = \mathbb{E}[\text{Prec}@R]$. Taking the expectation over $R$:

$$\mathbb{E}[\text{AP}] = \frac{1}{L}\sum_{r=1}^{L}\left(\frac{(r-1)(M-1)}{(L-1)r} + \frac{1}{r}\right)$$

Using the identities $\sum_{r=1}^{L}\frac{r-1}{r} = L - H_L$ and $\sum_{r=1}^{L}\frac{1}{r} = H_L$ completes the proof. $\square$

## 4. Corollaries and Implications

**Corollary 1.** *The expected AP can be expressed in terms of prevalence $p = M/L$ as:*

$$\mathbb{E}[\text{AP}] = p + (1-p)\frac{H_L - 1}{L-1}$$

**Corollary 2.** *As $L \to \infty$ with fixed prevalence $p$:*

$$\mathbb{E}[\text{AP}] = p + O\left(\frac{\log L}{L}\right) \to p$$

**Remark 1.** The finite-sample bias $\mathbb{E}[\text{AP}] - p = \frac{N(H_L-1)}{L(L-1)} > 0$ is strictly positive for all finite $L$, vanishing logarithmically as $L \to \infty$.

**Remark 2.** The null distribution depends on both $M$ and $L$ individually, not merely their ratio $p$. This explains why rankings with identical prevalence but different list lengths exhibit different statistical significance despite equal observed AP values: the sampling distribution narrows with increasing $L$ while maintaining approximately the same mean.

## 5. Conclusion

We have provided an exact closed-form expression for the expected Average Precision under random ranking, revealing a logarithmic finite-sample correction to the asymptotic prevalence limit. This result enables precise statistical inference for ranking algorithms and clarifies the role of sample size in significance testing.
