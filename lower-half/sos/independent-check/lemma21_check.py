"""Spot-check of SOS_RESULTS.md Lemma 2.1 (odd m): with A = X^2, B = Y^2, n = km, the alternating class
(A^k B)^m = (x^{2k} y^2)^m appears in u^* v (u, v half-words of bidegree (km, m)) only for u = v, and its
coefficient in p_{n,m} - (A^kB)^m is (k+1)/C(n+m,n) - 1 < 0; hence no pure cyclic SOS certificate for (F)."""
import math
import os
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from indep_core import cyc, all_words, poly_p  # noqa: E402


def main():
    out = []
    for k, m in [(1, 3), (2, 3), (3, 3), (4, 3), (1, 5)]:
        n = k * m
        C = cyc(('x' * (2 * k) + 'yy') * m)
        hw = all_words(k * m, m)
        hits = [(i, j) for i, u in enumerate(hw) for j, v in enumerate(hw) if cyc(u[::-1] + v) == C]
        diag_only = all(i == j for i, j in hits)
        coef = poly_p(n, m, 2, 2).get(C, Fraction(0)) - 1
        expected = Fraction(k + 1, math.comb(n + m, n)) - 1
        line = (f"(n,m)=({n},{m}) k={k}: {len(hw)} half-words, {len(hits)} pairs hit (A^kB)^m, all diagonal: {diag_only}; "
                f"coefficient in f = {coef} (Lemma: {expected}, equal: {coef == expected})")
        print(line, flush=True)
        out.append(line)
    with open(os.path.join(HERE, 'logs', 'lemma21_check.log'), 'w') as fh:
        fh.write('\n'.join(out) + '\n')


if __name__ == '__main__':
    main()
