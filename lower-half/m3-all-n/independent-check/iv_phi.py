"""Independent verifier, part 6: Taylor-coefficient enclosures of the scaled design function
    Phihat(z) = Phi(z) e^{mu z} = -sqrt(ys(z) ell(y(z))),   mu = (1/2 + lam)/2,   z >= 2,
    ys = y e^{(1/2+lam) z} = eta z (1 - q)/sqrt(G),   y = eta (1 - rr),   ell(y) = -log(1 - y)/y = sum_j y^j/(j+1),
with G, q as in iv_forms.py (own derivation; Phi^2 = -log(1 - y) = y ell(y)).
Coefficients at a thin point: arb power series of the closed form; on a ball: union over cells [k/128, (k+1)/128]
of centred-form enclosures  c_j(cell) in c_j(mid) + (j+1) c_{j+1}(cell ball) [-r, r]  (cells bisected if needed).
"""
from math import comb
import flint
from flint import arb, fmpq, arb_series
import iv_jet as JJ
from iv_jet import NotPos, ZERO, ONE

LAM = arb(7) / 100
ETA = arb(7) / 10
MU = (arb(1) / 2 + LAM) / 2
CELL = 128
_cache = {}


def _ell_coeffs(y0, K):
    """ell^(k)(y0)/k!, k = 0..K, for a ball |y0| <= 1/2: sum_{j>=k} C(j,k) y0^(j-k)/(j+1), j <= M, tail <= 3 x first
    omitted term (consecutive-term ratio <= (j+1)/(j+1-k) h <= 2/3 for j >= 4k, h <= 1/2)."""
    h = abs(y0).upper()
    if not (h <= 0.5):
        raise NotPos('ell: |y| > 1/2')
    M = 120
    out = []
    for k in range(K + 1):
        s = ZERO
        p = ONE
        for j in range(k, M + 1):
            s += comb(j, k) * p / (j + 1)
            p = p * y0
        tail = 3 * comb(M + 1, k) * arb(h) ** (M + 1 - k) / (M + 2)
        out.append(s + arb(0, tail.upper()))
    return out


def _compose_series(coeffs, s, L):
    """univariate composition f(s) for a series s with constant term s0, coeffs[k] = f^(k)(s0)/k! (k < L)."""
    c = s.coeffs()
    c = [c[i] if i < len(c) else ZERO for i in range(L)]
    t = arb_series([ZERO] + c[1:], prec=L)
    res = arb_series([coeffs[L - 1]], prec=L)
    for k in range(L - 2, -1, -1):
        res = res * t + coeffs[k]
    return res


def phihat_series(z0, K):
    """Taylor coefficients 0..K of Phihat at the ball z0 (plain ball arithmetic).  The closed form is an exact
    identity for every z > 0; it is cancellation-free only for z >= 2, so balls must lie in [2, inf), while thin
    points (used only for reference values, 200 bits) may be anywhere in z > 0."""
    if not (z0 >= arb(7) / 4 or (z0.rad() < 1e-40 and z0 > 0)):
        raise NotPos('phihat needs z >= 2 (or a thin z > 0)')
    L = K + 1
    flint.ctx.cap = L
    X = arb_series([z0, 1], prec=L)
    em = (-X).exp()
    G = 1 - (1 + X) * em - (X * X / 2) * (-(2 * X / 3)).exp()
    sG = G.sqrt()
    q = ((X - 1 + em) * (-((arb(1) / 2 - LAM) * X)).exp() / X + (X / 2) * (-((arb(1) / 6 - LAM) * X)).exp()) / (1 - em + sG)
    ys = ETA * X * (1 - q) / sG
    y = ys * (-((2 * MU) * X)).exp()
    yc = y.coeffs()
    el = _compose_series(_ell_coeffs(yc[0], K), y, L)
    P = ys * el
    pc = P.coeffs()
    if not (pc[0] > 0):
        raise NotPos('phihat: ys ell not positive')
    res = -(P.sqrt())
    c = res.coeffs()
    return [c[i] if i < len(c) else ZERO for i in range(L)]


def _cell(lo, hi, K):
    key = (lo, hi, K)
    if key in _cache:
        return _cache[key]
    mid = (lo + hi) / 2
    r = (hi - lo) / 2
    try:
        cm = phihat_series(arb(mid), K)
        cb = phihat_series(arb.union(arb(lo), arb(hi)), K + 1)
        out = [cm[j] + (j + 1) * cb[j + 1] * arb(0, arb(r)) for j in range(K + 1)]
        if max(float(x.rad()) for x in out) > 1e-4 and hi - lo > fmpq(1, 2 ** 14):
            raise NotPos('cell too wide')
    except NotPos:
        if hi - lo <= fmpq(1, 2 ** 14):
            raise
        u = _cell(lo, mid, K)
        v = _cell(mid, hi, K)
        out = [arb.union(x, y) for x, y in zip(u, v)]
    _cache[key] = out
    return out


def c_phihat(z0, K):
    if z0.rad() < 1e-40:
        return phihat_series(z0, K)
    from math import floor
    lo, hi = z0.lower(), z0.upper()
    k0 = int(floor(float(lo) * CELL)) - 1            # one extra cell on each side (no float-rounding gaps)
    k1 = int(floor(float(hi) * CELL)) + 1
    if not (fmpq(k0, CELL) <= fmpq(2)):
        pass
    if k0 < 224:                  # cells start at 7/4 (closed form exact for z > 0, well conditioned for z >= 7/4)
        if lo >= arb(7) / 4:
            k0 = 224
        else:
            raise NotPos('phihat cells below 7/4')
    parts = [_cell(fmpq(k, CELL), fmpq(k + 1, CELL), K) for k in range(k0, k1 + 1)]
    out = parts[0]
    for p in parts[1:]:
        out = [arb.union(x, y) for x, y in zip(out, p)]
    return out
