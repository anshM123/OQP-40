"""Theorem B: the double tail a >= 64, d >= 512, all eps in [0, 1/37].

Every quantity is enclosed by plain balls over cells of (m_a, w, eps) (m_a = nu_a - eps in [0, 1/64], w = 1/d in
[0, 1/512]); no centred form is needed.  With the notation of tb_tail2.py / tb_dtail.py:
  log F = -lam d + log(d nu_d) + (log nu_b - log nu_a)/2 - log(1+2eps) - (log om_a + log om_b)/2 + log(Dhat/d),
  Dhat/d = M^2 (1 + O(XA)) + O(XA),  M = phit_d - sqrt(1 + a w) phit_b e^{-mu a},
where phit_d = sqrt(eta) + O(1e-19) (Lemma T'), |sqrt(1 + a w) phit_b e^{-mu a}| and its Taylor coefficients are
<= 1.2 sqrt(1 + a/512) e^{-mu a} (1 + mu)^3 <= 1e-6 for a >= 64 (Lemma T), and
  nu_b in [eps, min(nu_a, nu_d)],  m_b = nu_b e^{-b eps} in [0, 1/(a + d)] subset [0, 1/576],
  log nu_a: a-jet (0, -m_a, nu_a m_a/2), log nu_b: b-jet (0, -m_b, nu_b m_b/2), nu_b: b-jet (nu_b, -nu_b m_b, ...).
Atoms (e^{-a}, e^{-a/3}/(c nu_a), e^{-b/3}/(c nu_b), e^{-b(1+2eps)}, ...): every Taylor coefficient in [-1e-6, 1e-6].
Usage: python tb_ddouble.py n_m n_w n_eps > log
"""
import sys
import time
from fractions import Fraction as Fr
from flint import arb, fmpq
import tb_arb as T
import tb_dtail as DT
from tb_arb import J, ZERO, ONE, MU, LAM, ETA

X6 = arb('1e-6')


def q(x):
    return arb(fmpq(x.numerator, x.denominator))


def unit(mode, mono):
    c = [ZERO] * mode.n
    c[mode.idx[mono]] = ONE
    return J(c, mode)


def atom(mode, X=X6):
    return J([arb(0, X)] * mode.n, mode)


def logF_double(m0, m1, w0, w1, e0, e1, mode=T.MP):
    eps = arb.union(q(e0), q(e1))
    cx = T.Ctx(eps)
    e2 = cx.e2
    ah, bh = unit(mode, (1, 0, 0)), unit(mode, (0, 1, 0))
    mA = arb.union(q(m0), q(m1))
    nua = mA + eps
    LNA = -mA * ah + nua * mA / 2 * ah * ah
    NUA = nua - nua * mA * ah + nua * mA * (nua + mA) / 2 * ah * ah
    oma = 1 - NUA / e2 + atom(mode)                       # nu_a e^{-a(1+2eps)}/(1+2eps) and e^{-a/3}/(c nu_a): atoms
    w = arb.union(q(w0), q(w1))
    md = DT.m_range(w0, w1, e0, e1)
    nd = md + eps
    LDN = DT.djet_from([ZERO, w - md, (-w * w + nd * md) / 2, (2 * w * w * w - nd * md * (nd + md)) / 6], mode)
    LIN = DT.djet_from([ZERO, ONE], mode)
    nub = arb.union(eps.lower(), arb.union(nua, nd).upper()) if True else None
    mb = arb.union(arb(0), arb(1) / 576)
    LNB = -mb * bh + nub * mb / 2 * bh * bh
    NUB = nub - nub * mb * bh + nub * mb * (nub + mb) / 2 * bh * bh
    omb = 1 - NUB / e2 + atom(mode)
    sq = ETA.sqrt()
    M = sq + atom(mode)
    DH = M * M * (1 + atom(mode)) + atom(mode)
    return -LAM * LIN + LDN + (LNB - LNA) / 2 - e2.log() - (oma.log() + omb.log()) / 2 + DH.log()


if __name__ == '__main__':
    n_m, n_w, n_eps = (int(x) for x in sys.argv[1:4])
    print(f"double tail: a >= 64 (m_a in [0, 1/64], {n_m} slices), d >= 512 (w in [0, 1/512], {n_w} slices), eps in [0, 1/37] ({n_eps} slabs)", flush=True)
    t0 = time.time()
    worst = [None] * 3
    bad = 0
    for i in range(n_m):
        for j in range(n_w):
            for k in range(n_eps):
                cell = (Fr(i, 64 * n_m), Fr(i + 1, 64 * n_m), Fr(j, 512 * n_w), Fr(j + 1, 512 * n_w), Fr(k, 37 * n_eps), Fr(k + 1, 37 * n_eps))
                L, _ = T.margins_from_logF(logF_double(*cell))
                for kk in range(3):
                    v = float(L[kk].lower())
                    if worst[kk] is None or v < worst[kk][0]:
                        worst[kk] = (v, tuple(float(x) for x in cell))
                if not all(l > 0 for l in L):
                    bad += 1
                    print("FAIL", [float(x) for x in cell], L, flush=True)
    print(f"cells: {n_m * n_w * n_eps}, failures: {bad}, time {time.time() - t0:.1f} s")
    for kk in range(3):
        print(f"  certified min lower bound of L{kk + 1}: {worst[kk][0]:.6g} on (m0, m1, w0, w1, e0, e1) = {worst[kk][1]}")
    print("RESULT: REGION VERIFIED" if bad == 0 else "RESULT: FAILED")
