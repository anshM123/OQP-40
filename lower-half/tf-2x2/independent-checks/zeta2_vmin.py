"""Is zeta_2 >= v_min = min_W ell for every non-commuting 2x2 pair? (Theorem A's case split assumes zeta_1 <= v_min <= zeta_2.)
det-normalised: A = exp(a x.sigma), B = exp(b y.sigma); W boundary traced by real unit vectors (real symmetric pair)."""
import numpy as np
rng = np.random.default_rng(7)
worst = np.inf
t = np.linspace(0, np.pi, 20001)
for trial in range(200000):
    th = rng.uniform(0.01, 0.5); a = rng.uniform(0, 8) * rng.random(); b = rng.uniform(0, 8) * rng.random()
    phi = rng.uniform(0, np.pi)          # angle between x and y in the Bloch picture: w = cos(phi)
    # Bloch vectors in the x-z plane; real unit vectors e(t) = (cos t, sin t) have Bloch vector (sin 2t, 0, cos 2t)
    ax = a * np.array([0.0, 1.0]); by = b * np.array([np.sin(phi), np.cos(phi)])   # (x-comp, z-comp)
    n = np.stack([np.sin(2 * t), np.cos(2 * t)], 1)
    Aval = np.cosh(a) + np.sinh(a) * (n @ np.array([0.0, 1.0]))
    Bval = np.cosh(b) + np.sinh(b) * (n @ np.array([np.sin(phi), np.cos(phi)]))
    vmin = np.min(th * np.log(Aval) + (1 - th) * np.log(Bval))
    zeta2 = np.linalg.norm(th * ax + (1 - th) * by)
    gap = zeta2 - vmin
    if gap < worst:
        worst = gap; arg = (th, a, b, np.cos(phi), zeta2, vmin)
print('min over 200000 random pairs of zeta_2 - v_min =', worst, 'at (theta,a,b,w,zeta2,vmin) =', arg)
