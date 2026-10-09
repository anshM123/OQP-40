"""Referee check, task 1 (a)-(d): re-derivation of the reduction chain for Theorem 4, in the referee's own notation.

Notation (referee's): A = sum_k alpha_k Q_k (distinct alpha_k > 0, spectral projections Q_k), B >= 0.
  T(i,j,k) := tr(B Q_i B Q_j B Q_k) = tr(W_i W_j W_k),  W_k := B^{1/2} Q_k B^{1/2}.
  f(A,B)  := tr(A^3B^3) + 2 Re tr(A^2BAB^2) - 3 tr((AB)^3).
Part A: exact symbolic algebra (sympy).  Part B: ball arithmetic (python-flint, 256 bits) on random instances,
with A diagonal (WLOG by unitary invariance) so that the Q_k are exact coordinate projections.
"""
import itertools, random, sys
import numpy as np
import sympy as sp
import mpmath as mp
from flint import arb, acb, acb_mat
sys.path.insert(0, '.')
from refutil import words33, word_trace, f33, p33_direct, diag_acb, herm_from_factor, tr, set_prec

out = []
def say(*a):
    s = ' '.join(str(x) for x in a)
    print(s, flush=True)
    out.append(s)

# ---------------------------------------------------------------- Part A: symbolic
x, y, z = sp.symbols('x y z', positive=True)
say('== A1. Kernel of p_{3,3} derived from the 20 words ==')
W = words33()
assert len(W) == 20 and len(set(W)) == 20
mono_sum = 0
for w in W:
    # rotate to start with 'B', then parse B A^c1 B A^c2 B A^c3
    k = w.index('B')
    r = w[k:] + w[:k]
    blocks = r.split('B')[1:]          # 3 blocks after the 3 B's
    c = [len(b) for b in blocks]
    assert len(c) == 3 and sum(c) == 3
    mono_sum += x**c[0] * y**c[1] * z**c[2]
perms = list(itertools.permutations((x, y, z)))
sym = sp.expand(sum(mono_sum.subs(dict(zip((x, y, z), p)), simultaneous=True) for p in perms) / 6)
M3 = sp.expand(sym / 20)
h3 = sum(x**a * y**b * z**(3 - a - b) for a in range(4) for b in range(4 - a))
say('  M3 (word average kernel, S3-symmetrised) == h_3/10 :', sp.simplify(M3 - h3 / 10) == 0)
kap = (x + y + z) * (x**2 + y**2 + z**2) - 9 * x * y * z
say('  10*(M3 - xyz) == kappa :', sp.expand(10 * (M3 - x * y * z) - kap) == 0)
say('  kappa(x,x,x) == 0 :', sp.expand(kap.subs({y: x, z: x})) == 0)
say('  kappa(x,y,y) == (x-y)^2 (x+4y) :', sp.expand(kap.subs(z, y) - (x - y)**2 * (x + 4 * y)) == 0)

# necklace classes
def rot(s, k): return s[k:] + s[:k]
classes = {}
for w in W:
    rep = min(rot(w, k) for k in range(6))
    classes.setdefault(rep, []).append(w)
say('  rotation classes (rep: size):', {k: len(v) for k, v in classes.items()})

say('== A2. Apex identity (6.1): kappa = sum_l (a-l)(b-l)(l+2a+2b) ==')
apex = (y - x) * (z - x) * (x + 2 * y + 2 * z) + (x - y) * (z - y) * (y + 2 * x + 2 * z) + (x - z) * (y - z) * (z + 2 * x + 2 * y)
say('  identity holds:', sp.expand(apex - kap) == 0)
# signs for x<y<z
s_y = (x - y) * (z - y) * (y + 2 * x + 2 * z)
say('  s_y = -(y-x)(z-y)(y+2x+2z):', sp.expand(s_y + (y - x) * (z - y) * (y + 2 * x + 2 * z)) == 0)

say('== A3. Lemma 6 formula: kappa(1,1+B,1+C) - cap = B^2 C G(B,C), B <= C ==')
Bs, Cs, p, q = sp.symbols('B C p q', positive=True)
kapE = kap.subs({x: 1, y: 1 + Bs, z: 1 + Cs}, simultaneous=True)
cap = Cs * (Cs - Bs) * p * q            # cap_c(1,b) = (c-1)(c-b) sqrt((c+4)(c+4b)),  p^2 = C+5, q^2 = C+4B+5
# claim: (kapE - cap) (p+q)^2 == B^2 [ (3C + B + 5)(p+q)^2 + 8 C (C-B) ]   (i.e. E_1 = B^2 C G, times (p+q)^2 / C)
lhs = sp.expand((kapE - cap) * (p + q)**2)
rhs = sp.expand(Bs**2 * ((3 * Cs + Bs + 5) * (p + q)**2 + 8 * Cs * (Cs - Bs)))
diff = sp.expand(lhs - rhs)
# exact reduction modulo p^2 = C+5, q^2 = C+4B+5 (by parity of exponents)
def reduce_pq(expr):
    P = sp.Poly(sp.expand(expr), p, q)
    res = 0
    for (i, j), c in P.terms():
        res += c * (Cs + 5)**(i // 2) * p**(i % 2) * (Cs + 4 * Bs + 5)**(j // 2) * q**(j % 2)
    return sp.expand(res)
say('  identity (reduced mod p^2=C+5, q^2=C+4B+5) == 0 :', reduce_pq(diff) == 0)
say('  E_1(b,b) = kappa(1,1+B,1+B) == B^2(4B+5) :', sp.expand(kap.subs({x: 1, y: 1 + Bs, z: 1 + Bs}) - Bs**2 * (4 * Bs + 5)) == 0)
# continuity of the formula at C = B: G(B,B) = 3 + (B+5)/B, B^2 * B * G(B,B) = B^2(4B+5)
say('  formula at C=B gives the diagonal:', sp.simplify(Bs**2 * Bs * (3 + (Bs + 5) / Bs) - Bs**2 * (4 * Bs + 5)) == 0)
# homogeneity of kappa and cap
lam = sp.symbols('lam', positive=True)
say('  kappa homogeneous deg 3:', sp.expand(kap.subs({x: lam * x, y: lam * y, z: lam * z}, simultaneous=True) - lam**3 * kap) == 0)

say('== A4. Derivatives of F = sqrt(B/C) G for arbitrary smooth G ==')
Gf = sp.Function('G')(Bs, Cs)
F = sp.sqrt(Bs / Cs) * Gf
FB = sp.diff(F, Bs); FC = sp.diff(F, Cs); FBC = sp.diff(F, Bs, Cs)
GB, GC, GBC = sp.diff(Gf, Bs), sp.diff(Gf, Cs), sp.diff(Gf, Bs, Cs)
chkB = sp.simplify(FB - (Bs**sp.Rational(-1, 2) * Cs**sp.Rational(-1, 2) / 2) * (Gf + 2 * Bs * GB))
chkC = sp.simplify(FC - (Bs**sp.Rational(1, 2) * Cs**sp.Rational(-3, 2) / 2) * (2 * Cs * GC - Gf))
chkBC = sp.simplify(FBC - (Bs**sp.Rational(-1, 2) * Cs**sp.Rational(-3, 2) / 4) * (-Gf - 2 * Bs * GB + 2 * Cs * GC + 4 * Bs * Cs * GBC))
say('  F_B formula:', chkB == 0, '  F_C formula:', chkC == 0, '  F_BC formula:', chkBC == 0)

# ---------------------------------------------------------------- Part B: ball arithmetic
set_prec(256)
say('== B. Ball-arithmetic checks on random instances (256-bit) ==')
rng = np.random.default_rng(20261009)
mp.mp.dps = 60

def kap_mp(a, b, c): return (a + b + c) * (a * a + b * b + c * c) - 9 * a * b * c

worst = {'p33': 0, 'Phi': 0, 'cert': 0, 'Rsym': 0}
min_R_eig, min_S_eig, min_G_eig = mp.inf, mp.inf, mp.inf
struct_ok = True
ntr = 120
for trial in range(ntr):
    r = int(rng.integers(1, 8)); mult = rng.integers(1, 4, size=r); d = int(mult.sum())
    alpha = np.sort(np.exp(rng.uniform(-4, 4, size=r)))
    if trial % 10 == 0 and r >= 2:          # nearly coincident eigenvalues
        alpha[1] = alpha[0] * (1 + 10.0 ** rng.uniform(-8, -3))
        alpha = np.sort(alpha)
    diagvals = np.repeat(alpha, mult)
    A = diag_acb([arb(float(v)) for v in diagvals])
    X = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
    X = X * np.exp(rng.uniform(-3, 3, size=d))  # column scaling -> spread spectrum of B
    B = herm_from_factor(X, delta=float(10.0 ** rng.uniform(-6, 0)))
    # projections
    idx = np.repeat(np.arange(r), mult)
    BQ = []
    for k in range(r):
        cols = [j for j in range(d) if idx[j] == k]
        BQk = acb_mat([[B[i, j] if j in cols else acb(0) for j in range(d)] for i in range(d)])
        BQ.append(BQk)
    # T(i,j,k)
    T = {}
    PP = {(i, j): BQ[i] * BQ[j] for i in range(r) for j in range(r)}
    for i, j, k in itertools.product(range(r), repeat=3):
        T[(i, j, k)] = tr(PP[(i, j)] * BQ[k])
    f, lhs, rhs, (t1, t2, t3) = f33(A, B)
    p33 = p33_direct(A, B)
    # 20 p = 6 t1 + 12 Re t2 + 2 t3
    e1 = abs(20 * p33.real - (6 * t1.real + 12 * t2.real + 2 * t3.real)).upper() / abs(t1.real).lower()
    alA = [arb(float(v)) for v in alpha]
    Phi = arb(0)
    for w in T:
        a_, b_, c_ = alA[w[0]], alA[w[1]], alA[w[2]]
        Phi += T[w].real * ((a_ + b_ + c_) * (a_ * a_ + b_ * b_ + c_ * c_) - 9 * a_ * b_ * c_)
    e2 = abs(Phi - 3 * f).upper() / max(abs(t1.real).lower(), 1e-300)
    e2b = abs(10 * (p33.real - t3.real) - 3 * f).upper() / max(abs(t1.real).lower(), 1e-300)
    worst['p33'] = max(worst['p33'], float(e1), float(e2b))
    worst['Phi'] = max(worst['Phi'], float(e2))
    # certificate
    al = [mp.mpf(float(v)) for v in alpha]
    total = arb(0)
    for l in range(r):
        others = [a for a in range(r) if a != l]
        n = len(others)
        if n == 0:
            continue
        R = [[T[(l, a, b)].real for b in others] for a in others]
        S = [[T[(l, a, b)] for b in others] for a in others]
        # symmetry R^(l)_ab = R^(a)_lb
        for ia, a in enumerate(others):
            for ib, b in enumerate(others):
                if a != b:
                    worst['Rsym'] = max(worst['Rsym'], float(abs(T[(l, a, b)].real - T[(a, l, b)].real).upper() / abs(t1.real).lower()))
        Gm = mp.matrix(n, n)
        for ia, a in enumerate(others):
            for ib, b in enumerate(others):
                xa, xb, xl = al[a], al[b], al[l]
                if a == b:
                    Gm[ia, ib] = kap_mp(xl, xa, xa)
                    if abs(Gm[ia, ib] - (xl - xa)**2 * (xl + 4 * xa)) > mp.mpf(10)**-40 * (1 + abs(Gm[ia, ib])):
                        struct_ok = False
                    continue
                lo, hi = min(xa, xb), max(xa, xb)
                if xl > hi:            # l is the largest point: cap
                    Gm[ia, ib] = (xl - lo) * (xl - hi) * mp.sqrt((xl + 4 * lo) * (xl + 4 * hi))
                    # equals u(a) u(b)
                    ua = (xl - xa) * mp.sqrt(xl + 4 * xa); ub = (xl - xb) * mp.sqrt(xl + 4 * xb)
                    if abs(Gm[ia, ib] - ua * ub) > mp.mpf(10)**-40 * (1 + abs(ua * ub)):
                        struct_ok = False
                elif xl < lo:          # l is the smallest point: the rest
                    capv = (hi - lo) * (hi - xl) * mp.sqrt((hi + 4 * lo) * (hi + 4 * xl))
                    Gm[ia, ib] = kap_mp(xl, lo, hi) - capv
                else:                  # middle
                    Gm[ia, ib] = mp.mpf(0)
        # PSD checks
        Rm = mp.matrix([[mp.mpf(float(v.mid())) for v in row] for row in R])
        Sm = mp.matrix([[mp.mpc(float(v.real.mid()), float(v.imag.mid())) for v in row] for row in S])
        dR = [mp.sqrt(abs(Rm[i, i])) if Rm[i, i] != 0 else mp.mpf(1) for i in range(n)]
        Rn = mp.matrix(n, n)
        Sn = mp.matrix(n, n)
        for i in range(n):
            for j in range(n):
                Rn[i, j] = Rm[i, j] / (dR[i] * dR[j]); Sn[i, j] = Sm[i, j] / (dR[i] * dR[j])
        min_R_eig = min(min_R_eig, min(mp.eigsy(Rn)[0]))
        min_S_eig = min(min_S_eig, min(mp.eighe(Sn)[0]))
        dG = [mp.sqrt(Gm[i, i]) for i in range(n)]
        Gn = mp.matrix(n, n)
        for i in range(n):
            for j in range(n):
                Gn[i, j] = Gm[i, j] / (dG[i] * dG[j])
        min_G_eig = min(min_G_eig, min(mp.eigsy(Gn)[0]))
        for ia in range(n):
            for ib in range(n):
                total += R[ia][ib] * arb(mp.nstr(Gm[ia, ib], 70))
    e3 = abs(total - f).upper() / max(abs(t1.real).lower(), 1e-300)
    worst['cert'] = max(worst['cert'], float(e3))
say(f'  {ntr} instances, r = 1..7 distinct eigenvalues of A, multiplicities 1..3, complex B (spread spectrum)')
say(f'  max rel err |20 p33 - (6t1+12Re t2+2t3)| and |10(p33-t3) - 3f| : {worst["p33"]:.2e}')
say(f'  max rel err |Phi_B(kappa) - 3 f|            : {worst["Phi"]:.2e}')
say(f'  max rel err |sum_l <R^(l),G^(l)> - f|      : {worst["cert"]:.2e}')
say(f'  max rel err |R^(l)_ab - R^(a)_lb|          : {worst["Rsym"]:.2e}')
say(f'  min normalised eigenvalue of R^(l) (real)   : {mp.nstr(min_R_eig, 5)}')
say(f'  min normalised eigenvalue of S^(l) (complex Hermitian, no Re): {mp.nstr(min_S_eig, 5)}')
say(f'  min normalised eigenvalue of certificate G^(l): {mp.nstr(min_G_eig, 5)}')
say(f'  certificate structure (diag = (l-a)^2(l+4a), below block = u u^T) exact to 1e-40: {struct_ok}')

# ---------------------------------------------------------------- B2: y^T R y = tr(W_l Y^2) with genuine W's
say('== B2. y^T R y = tr(W_l Y^2) for real y; complex y needs the Hermitian matrix S ==')
mp.mp.dps = 50
maxerr_real, maxerr_cplx, imag_seen = mp.mpf(0), mp.mpf(0), mp.mpf(0)
for trial in range(30):
    d = int(rng.integers(3, 7)); r = d
    Xr = mp.matrix([[mp.mpc(rng.normal(), rng.normal()) for _ in range(d)] for _ in range(d)])
    Bm = Xr * Xr.H
    E, V = mp.eighe(Bm)
    Bh = V * mp.diag([mp.sqrt(e) for e in E]) * V.H
    Wl = []
    for k in range(d):
        Qk = mp.zeros(d, d); Qk[k, k] = 1
        Wl.append(Bh * Qk * Bh)
    l = 0; others = list(range(1, d))
    yv = [mp.mpf(rng.normal()) for _ in others]
    Y = mp.zeros(d, d)
    for c, a in zip(yv, others):
        Y += c * Wl[a]
    val = sum((Wl[l] * Y * Y)[i, i] for i in range(d))
    quad = sum(yv[i] * yv[j] * mp.re(sum((Wl[l] * Wl[a] * Wl[b])[t, t] for t in range(d))) for i, a in enumerate(others) for j, b in enumerate(others))
    maxerr_real = max(maxerr_real, abs(val - quad) / abs(val))
    imag_seen = max(imag_seen, max(abs(mp.im(sum((Wl[l] * Wl[a] * Wl[b])[t, t] for t in range(d)))) for a in others for b in others if a != b))
    # complex y: y^* S y = tr(W_l Z^* Z), Z = sum y_a W_a
    yc = [mp.mpc(rng.normal(), rng.normal()) for _ in others]
    Z = mp.zeros(d, d)
    for c, a in zip(yc, others):
        Z += c * Wl[a]
    valc = sum((Wl[l] * Z.H * Z)[i, i] for i in range(d))
    quadc = sum(mp.conj(yc[i]) * yc[j] * sum((Wl[l] * Wl[a] * Wl[b])[t, t] for t in range(d)) for i, a in enumerate(others) for j, b in enumerate(others))
    maxerr_cplx = max(maxerr_cplx, abs(valc - quadc) / abs(valc))
say(f'  real y: max rel |y^T R y - tr(W_l Y^2)| = {mp.nstr(maxerr_real, 3)}  (tr(W_l Y^2) real, >= 0)')
say(f'  off-diagonal tr(W_l W_a W_b) have imaginary parts up to {mp.nstr(imag_seen, 3)} (so R needs Re to be a real symmetric matrix)')
say(f'  complex y: max rel |y^* S y - tr(W_l Z^*Z)| = {mp.nstr(maxerr_cplx, 3)}  (S = [tr(W_l W_a W_b)] is Hermitian PSD)')

open('r1_reduction.log', 'w').write('\n'.join(out) + '\n')
