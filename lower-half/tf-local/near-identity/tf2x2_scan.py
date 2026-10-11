"""Global TF scan for 2x2 pairs with the exact Bloch-sphere formula (independent of the moment SDP).
For each random pair and theta, evaluate T(u)/Tr(AB^r)-scale on a level grid covering [zeta_min - 1, max level on W];
print the minimum of T(u) / (GT/(N0(N0+1))), the ratio to the bottom-of-ray value."""
import sys, time
import numpy as np
from scipy.linalg import expm, logm, eigh
from tf2x2_sphere import tf_tail, bloch, plane_coords

seed = int(sys.argv[1]); budget = float(sys.argv[2])
rng = np.random.default_rng(seed)
t0 = time.time(); worst = (np.inf, None); k = 0
while time.time() - t0 < budget:
    sc = rng.choice([0.3, 1.0, 2.0, 3.0])
    X = rng.normal(size=(2, 2)) + 1j * rng.normal(size=(2, 2)); X = sc * (X + X.conj().T) / 2
    Y = rng.normal(size=(2, 2)) + 1j * rng.normal(size=(2, 2)); Y = sc * (Y + Y.conj().T) / 2
    A, B = expm(X), expm(Y)
    th = rng.choice([0.5, 0.4, 1 / 3, 0.25, 0.1])
    N0 = 1 / th; r = (1 - th) / th
    Z = th * X + (1 - th) * Y
    zeta = eigh(Z, eigvals_only=True)
    Br = expm(r * Y)
    GT = np.trace(A @ Br).real - np.trace(expm(X + r * Y)).real
    if GT <= 1e-9 * np.trace(A @ Br).real:
        continue
    a0, av = bloch(A); b0, bv = bloch(B)
    a2, b2 = plane_coords(av, bv)
    ang = np.linspace(0, 2 * np.pi, 721)
    top = max(th * np.log(a0 + a2 @ [np.cos(c), np.sin(c)]) + (1 - th) * np.log(b0 + b2 @ [np.cos(c), np.sin(c)]) for c in ang)
    us = np.concatenate([[zeta[0] - 1.0], np.linspace(zeta[0], zeta[-1], 13)])  # nontrivial range only
    base = GT / (N0 * (N0 + 1))
    for u in us:
        Tv, _ = tf_tail(A, B, th, u)
        rat = Tv / base
        if rat < worst[0]:
            worst = (rat, (k, th, u, zeta.tolist(), top))
    k += 1
    if k % 10 == 0:
        print(f"{time.time()-t0:7.0f}s pairs={k} worst T/base = {worst[0]:.6g} at {worst[1]}", flush=True)
print('FINAL pairs', k, 'worst', worst)
