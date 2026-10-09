"""POLYNOMIAL local rules for the m = 4 diagonal-share certificate.

A rule is a table gamma(p; q) over pairs p = (a,b), q = (i,j) of exponents (a<=b, i<=j, multiples of 1/qd, here
stored as integers in units 1/qd) with a+b+i+j = n, defining
    k(xy;ef) = sum over ORDERED (a,b),(i,j) of gamma x^a y^b e^i f^j.
Share identity: gamma(p;q) + gamma(q;p) = 2 kappa(p,q) (kappa = coefficient in K_n), gamma(p;p) = kappa(p,p).
Kernel lemma needed: C(x,y)_{ij} = sum_{(a,b) ordered} gamma((a,b);(i,j)) x^a y^b is PSD for all x, y > 0.
By homogeneity and symmetry: x = 1, y = t in (0, 1].
"""
from fractions import Fraction
from math import comb

import numpy as np


class Setup:
    def __init__(self, n, qd, lo=0, hi=None):
        self.n, self.qd = n, qd
        self.N = n * qd
        self.lo = lo
        self.hi = self.N if hi is None else hi
        self.expo = list(range(self.lo, self.hi + 1))
        self.C = comb(n + 3, 3)
        pbs = {}
        for a in self.expo:
            for b in self.expo:
                if a <= b:
                    pbs.setdefault(a + b, []).append((a, b))
        self.pairs_by_sum = pbs
        # live exponents for the kernel side: those i with some pair (a,b) summing to N - 2i
        self.live = [i for i in self.expo if (self.N - 2 * i) in pbs]
        liveset = set(self.live)
        self.var, self.fixed = [], {}
        seen = set()
        for s1, P1 in pbs.items():
            s2 = self.N - s1
            if s2 not in pbs:
                continue
            for p in P1:
                for q in pbs[s2]:
                    if p == q:
                        self.fixed[(p, q)] = self.kappa(p, q)
                    elif q[1] not in liveset:      # q dead as a kernel index: gamma(p;q) = 0
                        self.fixed[(p, q)] = 0.0
                        self.fixed[(q, p)] = 2 * self.kappa(p, q)
                    elif p[1] not in liveset:
                        continue                   # handled from the other side
                    elif (q, p) not in seen:
                        seen.add((p, q))
                        self.var.append((p, q))
        self.vidx = {k: t for t, k in enumerate(self.var)}
        self.E = list(self.live)

    def kappa(self, p, q, exact=False):
        a, b = p
        i, j = q
        qd, N = self.qd, self.N
        one = Fraction(1) if exact else 1.0
        v = 0 * one
        if all(z % qd == 0 and z >= 0 for z in (a, b, i, j)):
            v += one / self.C
        if 4 * a == N and a == b == i == j:
            v -= one
        return v

    def gamma(self, p, q, z, exact=False):
        key = (p, q)
        if key in self.fixed:
            if exact:
                if p == q:
                    return self.kappa(p, q, True)
                if q[1] not in self.live:
                    return 0 * self.kappa(p, q, True)
                return 2 * self.kappa(p, q, True)
            return self.fixed[key]
        if key in self.vidx:
            return z[self.vidx[key]]
        return 2 * self.kappa(p, q, exact) - z[self.vidx[(q, p)]]

    def Cmat_terms(self):
        """list over (ii,jj) of list of (pair (a,b), exponent-of-t list) giving C(1,t)_{ij}."""
        E = self.E
        out = {}
        for ii, i in enumerate(E):
            for jj, j in enumerate(E):
                if jj < ii:
                    continue
                ij = (min(i, j), max(i, j))
                s1 = self.N - i - j
                lst = []
                for (a, b) in self.pairs_by_sum.get(s1, []):
                    tex = [b, a] if a != b else [a]     # x=1: x^a y^b + x^b y^a -> t^b + t^a
                    lst.append(((a, b), ij, tex))
                out[(ii, jj)] = lst
        return out

    def C_numeric(self, z, t):
        E = self.E
        M = np.zeros((len(E), len(E)))
        for (ii, jj), lst in self.Cmat_terms().items():
            v = 0.0
            for p, ij, tex in lst:
                g = self.gamma(p, ij, z)
                v += g * sum(t ** (e / self.qd) for e in tex)
            M[ii, jj] = M[jj, ii] = v
        return M

    def k_value(self, z, x, y, e, f):
        """k(xy;ef) from the table (floating point)."""
        qd = self.qd
        tot = 0.0
        for s1, P1 in self.pairs_by_sum.items():
            s2 = self.N - s1
            if s2 not in self.pairs_by_sum:
                continue
            for (a, b) in P1:
                mx = x ** (a / qd) * y ** (b / qd) + (x ** (b / qd) * y ** (a / qd) if a != b else 0.0)
                for (i, j) in self.pairs_by_sum[s2]:
                    me = e ** (i / qd) * f ** (j / qd) + (e ** (j / qd) * f ** (i / qd) if i != j else 0.0)
                    tot += self.gamma((a, b), (i, j), z) * mx * me
        return tot
