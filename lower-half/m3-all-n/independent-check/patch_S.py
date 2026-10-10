"""In-memory correction of tb_arb.S_of for eps-jets of any eps-order (no file of the original folder is changed).

Original (tb_arb.py, first S_of):  S(x; eps0 + delta) = S(x; eps0) + delta S_eps(x; eps0)  -> every (i, j, 2) slot of the
jet is 0, although mode MT2 (DUAL_MODE) has (i, j, 2) slots and tighten() uses them for the (i, j, 1) slots.
Corrected:  S(x; eps0 + delta) = sum_{q <= ke} delta^q S^[q](x; eps0), S^[q] = (1/q!) d_eps^q S, with the x-Taylor
coefficients of S^[q] enclosed at every eps of the eps ball by tb_sx.g_S_q (exact eps-polynomials s_k, 120 terms,
Cauchy tails on |zeta - eps| <= 1/37).
"""
import os
import sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import flint
import tb_arb as T
import tb_sx as SX

_orig_S_of_J = T._S_of_J


def S_of_J_fixed(X, cx):
    if isinstance(cx.eps, T.J):
        ke = max(m[2] for m in X.m.monos)
        K = X.m.maxdeg
        gs = SX.g_S_q(X.c[0], cx.eps.c[0], ke, K)
        flint.ctx.cap = 64
        dE = T.J([T.ZERO] + cx.eps.c[1:], X.m)
        res = X.compose(gs[0])
        p = dE
        for qq in range(1, ke + 1):
            res = res + p * X.compose(gs[qq])
            p = p * dE
        return res
    return _orig_S_of_J(X, cx)


def install():
    T._S_of_J = S_of_J_fixed


def uninstall():
    T._S_of_J = _orig_S_of_J
