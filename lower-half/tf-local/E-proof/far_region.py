"""Far region max(x, y) >= L (s = x + y >= 0): rigorous constants for the analytic argument of PROOF.md, Section 6.
All numbers are computed with Arb balls (python-flint); the script asserts every inequality used."""
from flint import arb, ctx
import ecore as C

ctx.prec = 200
L = arb(10)
e = arb(1).exp()


def G0(x):
    """G0(x) = (phi(x) phi(-x) - 1)/x^2 = (2 cosh x - 2 - x^2)/x^4 = g(x, -x)."""
    return (2 * x.cosh() - 2 - x * x) / x ** 4


def mu(z):
    """mu(z) = 1/(1 - e^{-z}) - 1/z (mean of the density e^{zt}/phi(z) on [0,1]); increasing."""
    return 1 / (1 - (-z).exp()) - 1 / z


g0 = G0(L)
print("G0(10) =", g0.str(10))
c1 = arb(1) / 2                       # Case 1, |x|,|y| >= 1, xy < 0: tm <= theta/|xy| <= 1/2
c2 = e / (L - 1)                      # Case 1 near an axis: tm <= kappa*e/s <= e/(L-1)
c3 = (e - 1) / L                      # Case 2 near an axis: tm <= kappa*phi(1)/s <= (e-1)/L
print("bounds for tm: 1/2,", c2.str(8), ",", c3.str(8))
assert g0 > c1 and g0 > c2 and g0 > c3
dmu = mu(L) - mu(arb(-1))
print("mu(10) - mu(-1) =", dmu.str(10))
assert dmu > arb('0.48')
# Case 2, x >= L, y >= 1 (or symmetric):  need (1/2)(1/x + 1/y) <= 0.48 phi(x); worst case x = L, y = 1
lhs = (1 / L + 1) / 2
rhs = arb('0.48') * C.phi(L)
print("Case 2 check:", lhs.str(6), "<=", rhs.str(10))
assert lhs < rhs
# G0 increasing in |x| (even power series with positive coefficients) - stated in PROOF.md.
print("far-region constants: all assertions passed (L = 10)")
