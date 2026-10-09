"""Large-d 'free position' regime for the lower half of OQP 40 and conjecture (F):
A = diag(a), B = U diag(b) U^*, U Haar, d up to 120, spectra spread over several decades (bimodal, power-law).
Prints min ratios p/L and p/frac over the sampled cases."""
from math import comb

import numpy as np
from scipy.stats import unitary_group

rng = np.random.default_rng(17)


def word_average(A, B, n, m):
    d = A.shape[0]
    coeffs = [np.eye(d, dtype=complex)]
    for _ in range(n + m):
        new = [np.zeros((d, d), dtype=complex) for _ in range(len(coeffs) + 1)]
        for j, C in enumerate(coeffs):
            new[j] += C @ A
            new[j + 1] += C @ B
        coeffs = new
    return np.trace(coeffs[m]).real / comb(n + m, n)


def spectrum(d, kind):
    if kind == "bimodal":
        return np.where(rng.random(d) < 0.5, 1.0, 10 ** rng.uniform(-4, -1))
    if kind == "power":
        return 10 ** rng.uniform(-3, 0, size=d)
    return rng.uniform(0.05, 1.0, size=d)


worstL, worstF = np.inf, np.inf
for trial in range(60):
    d = int(rng.choice([20, 40, 80, 120]))
    ka, kb = rng.choice(["bimodal", "power", "flat"], size=2)
    a, b = spectrum(d, ka), spectrum(d, kb)
    U = unitary_group.rvs(d, random_state=rng)
    A = np.diag(a).astype(complex)
    B = U @ np.diag(b) @ U.conj().T
    H = np.diag(np.log(a))
    K = U @ np.diag(np.log(b)) @ U.conj().T
    for n, m in [(3, 3), (4, 4), (3, 5), (5, 5), (2, 7)]:
        p = word_average(A, B, n, m)
        L = np.sum(np.exp(np.linalg.eigvalsh(n * H + m * K)))
        S = np.diag(a ** (n / (2 * m)))
        F = np.sum(np.maximum(np.linalg.eigvalsh(S @ B @ S), 0) ** m)
        worstL, worstF = min(worstL, p / L), min(worstF, p / F)
    print(f"trial {trial} d={d} {ka}/{kb}: running min p/L = {worstL:.6f}, p/frac = {worstF:.6f}", flush=True)
