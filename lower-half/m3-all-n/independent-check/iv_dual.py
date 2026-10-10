"""Independent verifier, part 4: centre/box jet pairs with mean-value tightening (own implementation).

A TJ carries (c, b): c = the exact jet at the thin box centre, b = an enclosure of the jet at every point of the box
B = {centre + (x, y, z) : |x| <= ra, |y| <= rd, |z| <= re} in the coordinates (a, d, eps).  Every Taylor coefficient
Q_m (m = (i, j, k)) is a smooth function on the convex box, so by the mean value theorem, for every point of B,
    Q_m(point) = Q_m(c) + sum_v (m_v + 1) Q_{m + e_v}(xi) * delta_v,     |delta_v| <= r_v,
hence  b[m] may be replaced by  c[m] + sum_v (m_v + 1) b[m + e_v] [-r_v, r_v]  (intersected with b[m]) whenever all
three successors m + e_v exist in the jet space.  Applied after every product and before every univariate function.
The jet space is {(i,j,k): i + j + k <= 4, k <= 2}; eps is a full jet variable everywhere.
"""
from flint import arb
import iv_jet as JJ
from iv_jet import Jet, Space, ZERO, ONE

SP4 = Space(sorted({(i, j, k) for k in range(3) for i in range(5) for j in range(5) if i + j + k <= 4},
                   key=lambda m: (sum(m), m)))
_PLAN = []
for idx, m in enumerate(SP4.monos):
    succ = []
    ok = True
    for v in range(3):
        mm = list(m)
        mm[v] += 1
        j = SP4.idx.get(tuple(mm))
        if j is None:
            ok = False
            break
        succ.append((j, m[v] + 1))
    if ok:
        _PLAN.append((idx, succ))

RADII = [ZERO, ZERO, ZERO]       # balls [-r_v, r_v] of the current box (set by the driver)


def tighten(b, c):
    out = list(b.c)
    for idx, succ in _PLAN:
        t = c.c[idx]
        for v, (j, f) in enumerate(succ):
            t = t + (f * b.c[j]) * RADII[v]
        try:
            out[idx] = t.intersection(out[idx])
        except ValueError:          # two valid enclosures cannot be disjoint: treat as an error (box fails)
            raise JJ.NotPos('tighten: disjoint enclosures (bug?)')
    return Jet(out, b.sp)


class TJ:
    __slots__ = ('c', 'b')

    def __init__(self, c, b):
        self.c = c
        self.b = b

    def ball(self):
        return self.b.c[0]

    def __add__(x, y):
        if isinstance(y, TJ):
            return TJ(x.c + y.c, x.b + y.b)
        return TJ(x.c + y, x.b + y)
    __radd__ = __add__

    def __neg__(x):
        return TJ(-x.c, -x.b)

    def __sub__(x, y):
        if isinstance(y, TJ):
            return TJ(x.c - y.c, x.b - y.b)
        return TJ(x.c - y, x.b - y)

    def __rsub__(x, y):
        return (-x) + y

    def __mul__(x, y):
        if isinstance(y, TJ):
            c = x.c * y.c
            return TJ(c, tighten(x.b * y.b, c))
        return TJ(x.c * y, x.b * y)
    __rmul__ = __mul__

    def __truediv__(x, y):
        if isinstance(y, TJ):
            return x * y.recip()
        return TJ(x.c / y, x.b / y)

    def __rtruediv__(x, y):
        return x.recip() * y

    def _u(x, name):
        bt = tighten(x.b, x.c)
        return TJ(getattr(x.c, name)(), getattr(bt, name)())

    def exp(x):
        return x._u('exp')

    def log(x):
        return x._u('log')

    def sqrt(x):
        return x._u('sqrt')

    def recip(x):
        return x._u('recip')

    def phi1(x):
        return x._u('phi1')

    def neglog1m(x):
        return x._u('neglog1m')

    def phihat(x):
        return x._u('phihat')

    def final(x):
        """the box jet tightened once more (for reading off coefficients)."""
        return tighten(x.b, x.c)
