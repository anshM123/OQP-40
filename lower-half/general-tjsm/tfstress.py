import sys
import numpy as np
from scipy.linalg import expm
from tailtest import radial_tables
from tjsm import singular_points
from tftest import tf_curve

def report(A, B, label, thetas=(0.5, 1/3, 0.25, 0.2, 0.1), res=(400, 200)):
    PHI, R, MASS = radial_tables(A, B, *res)
    pts = singular_points(A, B)
    out = []
    for th in thetas:
        us, T, Tk, N0 = tf_curve(A, B, th, PHI, R, MASS, pts)
        ok = Tk > 1e-9 * Tk[0]
        rel = np.where(ok, T / np.where(ok, Tk, 1), np.inf)
        k = np.argmin(rel)
        # exact GT check at u=-inf: T(-inf) should equal (p - L)/(N0(N0+1)) at the min-exponent-1 point
        out.append(f"th={th:.2f}: minrel={rel[k]: .2e}@u={us[k]:.1f} rel(-inf)={rel[0]: .2e} minT={T.min(): .1e}")
    print(f"{label}: " + " | ".join(out), flush=True)

rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
# near-commuting pairs
for d in (3, 4):
    for eps in (0.3, 0.1, 0.03):
        a = np.exp(rng.normal(size=d)); b = np.exp(rng.normal(size=d))
        H = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d)); H = (H + H.conj().T) / 2
        U = expm(1j * eps * H)
        A = np.diag(a).astype(complex); B = U @ np.diag(b) @ U.conj().T
        report(A, B, f"near-comm d={d} eps={eps}")
# Cha-Lee family
for x, dl in [(0.3, 1e-2), (0.1, 1e-2), (0.1, 1e-3)]:
    A = np.array([[1 + dl, 0, 0], [0, x + dl, -x], [0, -x, x + dl]], dtype=complex)
    B = np.array([[x + dl, -x, 0], [-x, x + dl, 0], [0, 0, 1 + dl]], dtype=complex)
    report(A, B, f"Cha-Lee x={x} delta={dl}", res=(800, 400))
