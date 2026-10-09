"""Formal (exact, modulo cyclic rotation) check of the hand-checkable remarks in SOS_RESULTS.md section 1.1:
  F42: p_{4,2}(A,B) - tr(A^2B)^2 = (1/5)||[A^2,B]||^2 + (1/5)||A^{1/2}[A,B]A^{1/2}||^2,
  F24: p_{2,4}(A,B) - tr(A^{1/2}B)^4 = (1/5)||[A,B^2]||^2 + (1/5)||B^{1/2}[A,B]B^{1/2}||^2
                                       + (1/2)||[Z^*,Z]||^2 + (1/2)||Z^2 - Z^{*2}||^2,  Z = A^{1/2}B,
with A = X^2, B = Y^2 (so A^{1/2} = X, B^{1/2} = Y) and ||M||^2 = tr(M^* M)."""
import os
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from indep_core import cyc, poly_p, poly_sub, add_to  # noqa: E402


def P(*terms):
    """polynomial from (coeff, word) pairs."""
    out = {}
    for c, w in terms:
        add_to(out, w, Fraction(c))
    return out


def mul(a, b):
    out = {}
    for u, cu in a.items():
        for v, cv in b.items():
            add_to(out, u + v, cu * cv)
    return out


def add(a, b, s=1):
    out = dict(a)
    for k, v in b.items():
        add_to(out, k, s * v)
    return out


def star(a):
    return {k[::-1]: v for k, v in a.items()}          # real coefficients, Hermitian letters


def comm(a, b):
    return add(mul(a, b), mul(b, a), -1)


def norm2(M):
    """tr(M^* M) reduced modulo rotation."""
    out = {}
    for k, v in mul(star(M), M).items():
        add_to(out, cyc(k), v)
    return out


def scale(a, c):
    return {k: c * v for k, v in a.items()}


def main():
    A = P((1, 'xx'))
    B = P((1, 'yy'))
    X = P((1, 'x'))
    Y = P((1, 'y'))
    # F42
    lhs = poly_sub(poly_p(4, 2, 2, 2), {cyc('xxxxyy' * 2): Fraction(1)})
    A2 = mul(A, A)
    rhs = add(scale(norm2(comm(A2, B)), Fraction(1, 5)), scale(norm2(mul(mul(X, comm(A, B)), X)), Fraction(1, 5)))
    ok42 = (lhs == {k: v for k, v in rhs.items() if v != 0})
    # F24
    lhs24 = poly_sub(poly_p(2, 4, 2, 2), {cyc('xyy' * 4): Fraction(1)})
    B2 = mul(B, B)
    Z = mul(X, B)
    Zs = star(Z)
    r = add(scale(norm2(comm(A, B2)), Fraction(1, 5)), scale(norm2(mul(mul(Y, comm(A, B)), Y)), Fraction(1, 5)))
    r = add(r, scale(norm2(comm(Zs, Z)), Fraction(1, 2)))
    r = add(r, scale(norm2(add(mul(Z, Z), mul(Zs, Zs), -1)), Fraction(1, 2)))
    ok24 = (lhs24 == {k: v for k, v in r.items() if v != 0})
    msg = (f"F42 hand formula exact modulo rotation: {ok42}\n"
           f"F24 hand formula exact modulo rotation: {ok24}")
    print(msg)
    with open(os.path.join(HERE, 'logs', 'hand_formulas.log'), 'w') as fh:
        fh.write(msg + '\n')


if __name__ == '__main__':
    main()
