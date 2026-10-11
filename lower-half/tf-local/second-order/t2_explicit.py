"""Explicit second-order TF for a commuting 2x2 pair P1 = (a1,b1), P2 = (a2,b2) (rotation angle eps -> 0), ray theta.
Derived formula: T2(c) = int_0^1 w_c(l(u)) K(u) du, with
  Q(u) = u P1 + (1-u) P2, A(u) = theta log Qa, Bb(u) = (1-theta) log Qb, l = A + Bb,
  alpha = A(1)-A(0), beta = Bb(1)-Bb(0), Delta = alpha+beta,  K(u) = (alpha beta/Delta) l'(u) - A'(u) Bb'(u),
  w_c(v) = (N0 e^{N0 v} + c^{N0+1} e^{-v})/(N0+1) for v > log c, else 0;  N0 = 1/min(theta,1-theta).
Check: T2(c) must equal the eps^2 coefficient of the TF tail; compare its moments with D_k from tf_second_order."""
import sys
import numpy as np
from scipy import integrate

def T2(c, a1, b1, a2, b2, th):
    N0 = 1.0 / min(th, 1 - th)
    p, q = a1 - a2, b1 - b2
    Qa = lambda u: a2 + u * p
    Qb = lambda u: b2 + u * q
    l = lambda u: th * np.log(Qa(u)) + (1 - th) * np.log(Qb(u))
    Ap = lambda u: th * p / Qa(u)
    Bp = lambda u: (1 - th) * q / Qb(u)
    al, be = th * np.log(a1 / a2), (1 - th) * np.log(b1 / b2)
    De = al + be
    K = lambda u: (al * be / De) * (Ap(u) + Bp(u)) - Ap(u) * Bp(u)
    def w(v):
        return np.where(v > np.log(c) if c > 0 else True, (N0 * np.exp(N0 * v) + (c ** (N0 + 1)) * np.exp(-v)) / (N0 + 1), 0.0)
    f = lambda u: w(l(u)) * K(u)
    val, _ = integrate.quad(f, 0, 1, limit=400, points=None)
    return val

def moment_check(a, b, th, K):
    # moments: int e^{N v} d(Pi2 * k) tilted... compare N^2 * int e^{N l} K du  with  delta2(N) = (p - L)_2 at N = (k+1) N0
    N0 = 1.0 / min(th, 1 - th)
    out = []
    for k in range(K + 1):
        N = (k + 1) * N0
        p_, q_ = a - 1.0, b - 1.0
        f = lambda u: np.exp(N * (th * np.log(1 + u * p_) + (1 - th) * np.log(1 + u * q_))) * (
            (th * np.log(a) * (1 - th) * np.log(b) / (th * np.log(a) + (1 - th) * np.log(b))) * (th * p_ / (1 + u * p_) + (1 - th) * q_ / (1 + u * q_))
            - th * p_ / (1 + u * p_) * (1 - th) * q_ / (1 + u * q_))
        val, _ = integrate.quad(f, 0, 1, limit=400)
        out.append(N * N * val / (N * (N + 1)))
    return out

if __name__ == '__main__':
    import mpmath as mp
    from tf_second_order import D_seq
    for (a, b) in [(2.0, 3.0), (0.3, 5.0), (5.0, 0.2), (0.5, 0.4), (10.0, 1.7)]:
        D = D_seq(mp.mpf(a), mp.mpf(b), 1, 6)
        Mexp = moment_check(a, b, 0.5, 6)   # P1 = (a, b), P2 = (1, 1), theta = 1/2
        print(f"(a,b)=({a},{b}): exact eps^2 moments D_k vs formula:", ["%.10g/%.10g" % (float(x), y) for x, y in zip(D[:4], Mexp[:4])], flush=True)
