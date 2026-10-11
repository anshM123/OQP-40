"""Independent check of the 2x2 reduction (Theorem A of tf2x2_proof/PROOF.md):
   min_u T(u)  ==  C(min(u_c, v_min)) / (N0(N0+1))   when this is the binding value,
with C(u) = Tr(AB^r) - e^{N0 zeta_2} - (N0+1) e^{N0 u} + N0 e^{(N0+1)u} c,  c = G - e^{-zeta_2},
G = Tr(A^{-1} #_{1-th} B^{-1}), u_c = -log c, v_min = min of l over the joint numerical range.
T(u) is computed with the exact Bloch-sphere formula (tf-local/near-identity/tf2x2_sphere.py), independent of the proof code."""
import os
import sys
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'tf-local', 'near-identity'))
from tf2x2_sphere import tf_tail

def fun(M, f):
    w, V = np.linalg.eigh((M + M.conj().T) / 2); return (V * f(w)) @ V.conj().T

def closed_form(A, B, th):
    N0 = 1 / th; r = (1 - th) / th
    X, Y = fun(A, np.log), fun(B, np.log)
    zeta = np.linalg.eigvalsh(th * X + (1 - th) * Y)
    P = np.trace(A @ fun(B, lambda x: x ** r)).real
    Ai, Bi = fun(A, lambda x: 1 / x), fun(B, lambda x: 1 / x)
    Ah, Amh = fun(Ai, np.sqrt), fun(Ai, lambda x: x ** -0.5)
    G = np.trace(Ah @ fun(Amh @ Bi @ Amh, lambda x: x ** (1 - th)) @ Ah).real
    c = G - np.exp(-zeta[1])
    uc = -np.log(c)
    # v_min over the joint numerical range: minimise over unit vectors (Bloch sphere grid)
    th_g, ph_g = np.meshgrid(np.linspace(0, np.pi, 801), np.linspace(0, 2 * np.pi, 801), indexing='ij')
    psi = np.stack([np.cos(th_g / 2), np.sin(th_g / 2) * np.exp(1j * ph_g)], axis=-1).reshape(-1, 2)
    la = np.einsum('ij,jk,ik->i', psi.conj(), A, psi).real; lb = np.einsum('ij,jk,ik->i', psi.conj(), B, psi).real
    vmin = np.min(th * np.log(la) + (1 - th) * np.log(lb))
    ustar = min(uc, vmin)
    C = P - np.exp(N0 * zeta[1]) - (N0 + 1) * np.exp(N0 * ustar) + N0 * np.exp((N0 + 1) * ustar) * c
    return C / (N0 * (N0 + 1)), ustar, zeta, vmin, uc

rng = np.random.default_rng(12)
for trial in range(8):
    X0 = rng.normal(size=(2, 2)) + 1j * rng.normal(size=(2, 2)); X0 = (X0 + X0.conj().T) / 2
    Y0 = rng.normal(size=(2, 2)) + 1j * rng.normal(size=(2, 2)); Y0 = (Y0 + Y0.conj().T) / 2
    s = [0.3, 0.7, 1.2, 0.5][trial % 4]; th = [0.5, 0.35, 0.25, 0.5][trial % 4]
    A, B = fun(s * X0, np.exp), fun(s * Y0, np.exp)
    cf, ustar, zeta, vmin, uc = closed_form(A, B, th)
    us = np.linspace(zeta[0] - 0.05 * (zeta[1] - zeta[0]), zeta[1], 81)
    Ts = np.array([tf_tail(A, B, th, u)[0] for u in us])
    k = int(np.argmin(Ts))
    Tst = tf_tail(A, B, th, ustar)[0]
    where = 'u = zeta_2 (right end; T(zeta_2) >= 0 trivially)' if k == len(us) - 1 else f'u = {us[k]:.4f}'
    print(f"trial {trial} th={th}: zeta = ({zeta[0]:.4f}, {zeta[1]:.4f}); u_c = {uc:.4f}, v_min = {vmin:.4f}, "
          f"u* = {ustar:.4f}\n    closed form C(u*)/(N0(N0+1)) = {cf:.9e},  exact T(u*) = {Tst:.9e}\n"
          f"    grid minimum of T on [zeta_1 - 0.05 gap, zeta_2]: {Ts[k]:.6e} at {where}", flush=True)
