"""Direct check of T(h gamma) ~ h^3 tau(gamma) near the identity (2x2, exact sphere formula)."""
import numpy as np
from scipy.linalg import expm, eigh
from tf2x2_sphere import tf_tail

rng = np.random.default_rng(4)
X = rng.normal(size=(2, 2)) + 1j * rng.normal(size=(2, 2)); X = (X + X.conj().T) / 2
Y = rng.normal(size=(2, 2)) + 1j * rng.normal(size=(2, 2)); Y = (Y + Y.conj().T) / 2
for th in (0.5, 0.3):
    S = th * X + (1 - th) * Y
    s, U = eigh(S)
    T = U.conj().T @ (X - Y) @ U
    w = abs(T[0, 1]) ** 2
    def tau(g):
        return th * (1 - th) / 2 * w * max(s[1] - g, 0) * max(g - s[0], 0) / (s[1] - s[0])
    print(f"theta={th}: s = {s}")
    for frac in (0.25, 0.5, 0.75):
        g = s[0] + frac * (s[1] - s[0])
        row = []
        for h in (0.08, 0.04, 0.02):
            A, B = expm(h * X), expm(h * Y)
            Tv, _ = tf_tail(A, B, th, h * g)
            row.append(Tv / h ** 3 / tau(g))
        print(f"  gamma at {frac:.2f} of the gap: T/(h^3 tau) for h = 0.08, 0.04, 0.02: " + ", ".join(f"{r:.6f}" for r in row))
