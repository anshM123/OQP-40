"""Is n -> p_{n,m}(A,B) (fixed m) a Hausdorff/Stieltjes moment sequence?  Equivalently: is the 'A-marginal'
pi'_m = sum_i beta(i) * (B-spline with knots alpha_{i_1..i_m}) a positive measure?
Exact test for m = 3: evaluate the density of pi'_3 on a fine grid directly from the cycle expansion
(B-spline of 3 knots = piecewise-linear 'hat' density), in A's eigenbasis.  Negative values => not a measure.
Also Hankel PSD test from moments for m = 3, 4 (mpmath, 60 digits)."""
import itertools

import mpmath as mp
import numpy as np

rng = np.random.default_rng(23)
mp.mp.dps = 60


def bspline3(t, x):
    """Density of u1 x1 + u2 x2 + u3 x3, u ~ Dirichlet(1,1,1): piecewise linear, integrates to 1."""
    a, b, c = sorted(x)
    if c - a < 1e-14:
        return None                                   # atom (all equal) handled separately
    if t <= a or t >= c:
        return 0.0
    # density of the 3-knot B-spline normalised to mass 1:  2 * (t - a) / ((c - a)(b - a)) on [a,b], etc.
    if b - a < 1e-14:
        return 2 * (c - t) / (c - a) ** 2
    if c - b < 1e-14:
        return 2 * (t - a) / (c - a) ** 2
    if t <= b:
        return 2 * (t - a) / ((c - a) * (b - a))
    return 2 * (c - t) / ((c - a) * (c - b))


worst = np.inf
for trial in range(300):
    d = int(rng.integers(3, 6))
    X = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
    B = X @ X.conj().T / d                              # PSD, in A's eigenbasis
    alpha = np.sort(rng.uniform(0, 1, size=d))
    grid = np.linspace(alpha[0], alpha[-1], 801)[1:-1]
    dens = np.zeros_like(grid)
    for i, j, k in itertools.product(range(d), repeat=3):
        if i == j == k:
            continue
        beta = (B[i, j] * B[j, k] * B[k, i]).real if (i, j, k) else 0
        # sum over all 3-cycles: use full complex beta and take real part at the end (pairs (ijk),(ikj) conjugate)
        beta = B[i, j] * B[j, k] * B[k, i]
        vals = np.array([bspline3(t, (alpha[i], alpha[j], alpha[k])) for t in grid])
        dens = dens + (beta * vals).real
    m = dens.min() / max(dens.max(), 1e-300)
    worst = min(worst, m)
print(f"m=3: min over 300 random cases of (min density / max density) of the continuous part of pi'_3 = {worst:.4e}")
print("    (negative => pi'_3 is a signed measure, so n -> p_{n,3} is not a moment sequence in general)")
