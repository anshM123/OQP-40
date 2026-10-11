"""NUMERICAL exploration: shape of T(u) for 2x2 pairs vs the closed-form reduction.
Ansh Mishra, Aryan Senthilkumar.
Compares the exact Bloch-sphere value T(u) (reference tf2x2_sphere.tf_tail) with C(u)/(N0(N0+1)) on [zeta_1, v_min],
and checks that min_u T(u) = C(min(u_c, v_min))/(N0(N0+1)) when u_c < v_min."""
import sys, os
import numpy as np
import mpmath as mp
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'tf-local', 'near-identity'))
from tf2x2_sphere import tf_tail
from cf2x2 import quantities, C_of_u, Dc, vmin_vmax

SZ = np.array([[1, 0], [0, -1]], complex)
SX = np.array([[0, 1], [1, 0]], complex)


def mats(al, be, ga):
    A = np.eye(2) + al * SZ
    B = np.eye(2) + be * (np.cos(ga) * SZ + np.sin(ga) * SX)
    return A, B


rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
ntr = int(sys.argv[2]) if len(sys.argv) > 2 else 6
for k in range(ntr):
    th = float(rng.choice([0.5, 0.4, 1 / 3, 0.25, 0.1]))
    al, be = rng.uniform(0.05, 0.95, 2)
    ga = rng.uniform(0.1, np.pi - 0.1)
    q = quantities(th, al, be, ga)
    vmin, vmax = vmin_vmax(q)
    N0 = 1 / th
    A, B = mats(al, be, ga)
    z1, z2 = float(q['z1']), float(q['z2'])
    uc = float(q['uc'])
    print(f"--- th={th:.3f} al={al:.3f} be={be:.3f} ga={ga:.3f}: zeta=({z1:.4f},{z2:.4f}) vmin={float(vmin):.4f} "
          f"vmax={float(vmax):.4f} uc={uc:.4f}  Dc={float(Dc(q)):.4e}  GT={float(q['GT']):.3e} AH={float(q['AH']):.3e}")
    # check closed form on [zeta_1, vmin]
    for u in np.linspace(z1, float(vmin), 3):
        Tv, _ = tf_tail(A, B, th, u)
        print(f"   u={u: .4f}: T sphere = {Tv: .10e}   C/(N0(N0+1)) = {float(C_of_u(q, u)) / (N0 * (N0 + 1)): .10e}")
    # scan T over [zeta_1, zeta_2]
    us = np.linspace(z1, z2, 41)
    Ts = [tf_tail(A, B, th, u)[0] for u in us]
    i = int(np.argmin(Ts))
    pred = float(C_of_u(q, min(uc, float(vmin)))) / (N0 * (N0 + 1))
    print(f"   grid min T = {Ts[i]:.6e} at u = {us[i]:.4f} (index {i}/40); predicted min over [z1,vmin] = {pred:.6e}; "
          f"T(z2) = {Ts[-1]:.4e}")
