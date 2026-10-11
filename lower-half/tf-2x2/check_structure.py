"""NUMERICAL check of the structural lemma for 2x2 pairs.
Ansh Mishra, Aryan Senthilkumar.

Claim (Lemma S): on (v_min, v_max) the function Lambda(u) := <Pi, 1[l > u]> satisfies Lambda <= 1, so that
e^{-u} f(u) is nondecreasing on (v_min, zeta_2), where f = m - kappa and T'(u) = -e^{N0 u} f(u).
Here Lambda(u) is computed directly from the disk representation of Pi:
  Lambda(u) = 1 - (1/pi) * int_{lens} (1 - |y|^2)^{-3/2} dy      (one chord case),
and independently f is obtained from finite differences of the exact tail T (tf2x2_sphere.tf_tail).
"""
import sys, os
import numpy as np
from scipy import integrate, optimize
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'tf-local', 'near-identity'))
from tf2x2_sphere import tf_tail
import mpmath as mp
from cf2x2 import quantities, vmin_vmax

SZ = np.array([[1, 0], [0, -1]], complex)
SX = np.array([[0, 1], [1, 0]], complex)


def lev_disk(th, al, be, ga, y1, y2):
    return th * np.log(1 + al * y1) + (1 - th) * np.log(1 + be * (np.cos(ga) * y1 + np.sin(ga) * y2))


def Lambda_direct(th, al, be, ga, u, n=200):
    """Lambda(u) = (1/pi)[ int_{K cap D} w dy + int_{Gamma} (y.n_in) w ds ], w = (1-|y|^2)^{-1/2}, K = {l > u},
    via polar coordinates around the origin of the disk: along each ray the set {l > u} is an interval (concave l).
    Equivalent volume form: Lambda = (1/pi) int_D (1 + y.grad) 1_K w dy computed as the limit of a smoothed indicator."""
    # smoothed indicator H_eps(l - u) with H_eps -> 1[> 0]; use the exact formula for C^1 F:
    # <Pi, F> = (1/pi) int_0^{2pi} int_0^{pi/2} [d/drho (rho F)](sin psi) sin psi dpsi dphi
    eps = 1e-4
    def F(l):
        z = (l - u) / eps
        return 0.5 * (1 + np.tanh(z))
    def dF(l):
        z = (l - u) / eps
        return 0.5 / eps / np.cosh(z) ** 2
    def inner(phi):
        c, s = np.cos(phi), np.sin(phi)
        def g(psi):
            rho = np.sin(psi)
            y1, y2 = rho * c, rho * s
            a = 1 + al * y1; b = 1 + be * (np.cos(ga) * y1 + np.sin(ga) * y2)
            l = th * np.log(a) + (1 - th) * np.log(b)
            dl = th * al * c / a + (1 - th) * be * (np.cos(ga) * c + np.sin(ga) * s) / b  # d l / d rho
            return (F(l) + rho * dF(l) * dl) * rho
        # split where l crosses u along the ray
        ps = np.linspace(0, np.pi / 2, 401)
        vals = np.array([lev_disk(th, al, be, ga, np.sin(p) * c, np.sin(p) * s) - u for p in ps])
        edges = [0.0]
        for i in range(len(ps) - 1):
            if vals[i] * vals[i + 1] < 0:
                r0 = optimize.brentq(lambda p: lev_disk(th, al, be, ga, np.sin(p) * c, np.sin(p) * s) - u, ps[i], ps[i + 1])
                edges += [max(r0 - 40 * eps, edges[-1]), min(r0 + 40 * eps, np.pi / 2)]
        edges.append(np.pi / 2)
        edges = sorted(set(edges))
        return sum(integrate.quad(g, lo, hi, limit=200, epsabs=1e-12)[0] for lo, hi in zip(edges[:-1], edges[1:]))
    return integrate.quad(inner, 0, 2 * np.pi, limit=400, epsabs=1e-10)[0] / np.pi


rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 3)
ntr = int(sys.argv[2]) if len(sys.argv) > 2 else 3
for k in range(ntr):
    th = float(rng.choice([0.5, 0.4, 0.25]))
    al, be = rng.uniform(0.2, 0.9, 2); ga = rng.uniform(0.3, np.pi - 0.3)
    q = quantities(th, al, be, ga)
    vmin, vmax = [float(v) for v in vmin_vmax(q)]
    z1, z2 = float(q['z1']), float(q['z2'])
    N0 = 1 / th
    A = np.eye(2) + al * SZ; B = np.eye(2) + be * (np.cos(ga) * SZ + np.sin(ga) * SX)
    print(f"--- th={th} al={al:.3f} be={be:.3f} ga={ga:.3f}: z1={z1:.4f} vmin={vmin:.4f} z2={z2:.4f} vmax={vmax:.4f} uc={float(q['uc']):.4f}")
    us = np.linspace(vmin + 1e-3, z2 - 1e-3, 9)
    for u in us:
        Lam = Lambda_direct(th, al, be, ga, u)
        h = 1e-4
        Tp, _ = tf_tail(A, B, th, u + h); Tm, _ = tf_tail(A, B, th, u - h)
        f = -(Tp - Tm) / (2 * h) * np.exp(-N0 * u)
        print(f"   u={u: .4f}: Lambda={Lam:.6f} (<=1?)  e^-u f = {np.exp(-u) * f: .8e}")
