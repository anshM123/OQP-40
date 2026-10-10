import sys
import numpy as np
from tailtest import radial_tables
from tjsm import singular_points
from tftest import tf_curve
seed = int(sys.argv[1]) if len(sys.argv) > 1 else 0
rng = np.random.default_rng(seed)
def rand_pd(d, spread):
    X = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
    Q, _ = np.linalg.qr(X)
    return (Q * np.exp(spread * rng.normal(size=d))) @ Q.conj().T
for trial in range(10):
    d = [2, 2, 3, 3, 4, 4, 5, 3, 4, 3][trial]; sp = [1, 2, 1, 2, 1, 2, 1, 3, 3, 0.5][trial]
    A, B = rand_pd(d, sp), rand_pd(d, sp)
    PHI, R, MASS = radial_tables(A, B, 400, 200)
    pts = singular_points(A, B)
    res = []
    for th in (0.5, 1/3, 0.25, 0.2):
        us, T, Tk, N0 = tf_curve(A, B, th, PHI, R, MASS, pts)
        ok = Tk > 1e-9 * Tk[0]
        rel = np.where(ok, T / np.where(ok, Tk, 1), np.inf)
        k = np.argmin(rel)
        res.append(f"th={th:.3f}: min T/Tk={rel[k]: .2e} (u={us[k]:.2f}); minT={T.min(): .1e}")
    print(f"[d={d} sp={sp}] " + " | ".join(res), flush=True)
