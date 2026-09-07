"""Compare the published full-list variance with the repository expression.

Run: uv run python verify.py
Source: https://www.vmsta.org/journal/VMSTA/article/353/text, Theorem 1.
Specialization: k=N=L, m=M; valid as rational functions for L >= 4, M >= 1.
Small-list boundary cases are covered separately by the demo.py enumeration.
"""

import sympy as s

L, M, H, H2 = s.symbols("L M H H2")
p = M / L
q = (M - 1) / (L - 1)
r = (M - 2) / (L - 2)
t = (M - 3) / (L - 3)

# Coefficients A-G of the published Theorem 1.
A = 1 - p - q * (3 - 2 * r - p * (2 - q))
B = q * (3 * (1 - r) - 2 * p * (1 - q))
C = q * (r - p * q)
D = q * (2 - 5 * r + 3 * r * t) - p * (1 - q) ** 2
E = q * (3 * r * (1 - t) - p * (1 - q))
F = q * (r * (1 - t) - p * (1 - q))
G = q * (r * t - p * q)
published = (
    p
    / M**2
    * (
        L * (C + 2 * (E - F) + (L - 1) * G)
        + H * (B - 2 * (E - L * F))
        + H**2 * D
        + H2 * (A - D)
    )
)

# Inclusion-probability expression in main.tex.
m1, m2, m3, m4 = p, p * q, p * q * r, p * q * r * t
ew = m1 * H + m2 * (L - H)
ew2 = (
    m1 * H2
    + m2 * (2 * H**2 + 3 * H - 5 * H2)
    + m3 * (2 * L * H + 5 * L - 5 * H**2 - 9 * H + 7 * H2)
    + m4 * (L**2 - 2 * L * H - 5 * L + 3 * H**2 + 6 * H - 3 * H2)
)
difference = s.factor(published - (ew2 - ew**2) / M**2)
assert difference == 0, difference
print("Published full-list variance minus repository variance = 0 (symbolically).")


# Independently enumerate the deterministic coefficient sums in Appendix A.
from fractions import Fraction
from itertools import product

from moments import harmonic

for length in range(1, 16):
    sums = [Fraction(0) for _ in range(5)]
    terms = [(i, k) for k in range(1, length + 1) for i in range(1, k + 1)]
    for (i, k), (j, l) in product(terms, repeat=2):
        sums[len({i, k, j, l})] += Fraction(1, k * l)
    h, h2 = harmonic(length), harmonic(length, 2)
    expected = [
        h2,
        2 * h * h + 3 * h - 5 * h2,
        2 * length * h + 5 * length - 5 * h * h - 9 * h + 7 * h2,
        length * length - 2 * length * h - 5 * length + 3 * h * h + 6 * h - 3 * h2,
    ]
    assert sums[1:] == expected, length
print("Four coefficient sums match exact enumeration for L=1..15.")
