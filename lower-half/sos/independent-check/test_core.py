"""Self-tests of indep_core (run before trusting it)."""
import os
import random
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from indep_core import (cyc, dih, least_rotation, poly_p, poly_pmult, poly_pmult_bruteforce, frac_word,
                        is_reversal_symmetric, ldl_pd_exact, psd_exact, all_words)


def brute_cyc(w):
    return min(w[i:] + w[:i] for i in range(len(w)))


def main():
    rng = random.Random(12345)
    # 1. Booth vs brute force, including periodic words
    n_tests = 0
    for L in range(1, 25):
        for _ in range(400):
            w = ''.join(rng.choice('xy') for _ in range(L))
            assert cyc(w) == brute_cyc(w), w
            n_tests += 1
        for per in range(1, L + 1):
            if L % per == 0:
                base = ''.join(rng.choice('xy') for _ in range(per))
                w = base * (L // per)
                assert cyc(w) == brute_cyc(w), w
                n_tests += 1
    # exhaustive for length <= 14
    for L in range(1, 15):
        for i in range(2 ** L):
            w = ''.join('y' if (i >> b) & 1 else 'x' for b in range(L))
            assert cyc(w) == brute_cyc(w)
            n_tests += 1
    print(f"Booth least rotation agrees with brute force on {n_tests} words")

    # 2. p^mult via compositions == via J enumeration
    for (n, m, ea, eb) in [(3, 3, 2, 2), (4, 4, 2, 2), (3, 4, 4, 2), (6, 4, 2, 2), (2, 4, 2, 2), (4, 2, 2, 2), (5, 3, 1, 1)]:
        a = poly_pmult(n, m, ea, eb)
        b = poly_pmult_bruteforce(n, m, ea, eb)
        assert a == b, (n, m)
        assert sum(a.values()) == 1
        print(f"p^mult_{{{n},{m}}}(X^{ea},Y^{eb}): compositions == brute force over [m]^n ({len(a)} cyclic classes), total weight 1")

    # 3. necklace identity for p_{3,3}: 20 p = 6 A^3B^3 + 6 A^2BAB^2 + 6 A^2B^2AB + 2 (AB)^3 (letters A=x, B=y)
    p33 = poly_p(3, 3, 1, 1)
    expect = {cyc('xxxyyy'): Fraction(6, 20), cyc('xxyxyy'): Fraction(6, 20), cyc('xxyyxy'): Fraction(6, 20),
              cyc('xyxyxy'): Fraction(2, 20)}
    assert p33 == expect, p33
    assert cyc('xxyyxy') == cyc('xxyxyy'[::-1])
    assert cyc('xxyyxy') != cyc('xxyxyy')
    print("p_{3,3}: 20 p = 6 tr A^3B^3 + 6 tr A^2BAB^2 + 6 tr A^2B^2AB + 2 tr (AB)^3; AABBAB is the reversal class of AABABB")

    # 4. targets are reversal symmetric
    for (n, m, ea, eb) in [(4, 4, 2, 2), (3, 4, 4, 2), (6, 4, 2, 2), (2, 4, 2, 2), (4, 2, 2, 2)]:
        assert is_reversal_symmetric(poly_p(n, m, ea, eb))
        assert is_reversal_symmetric(poly_pmult(n, m, ea, eb))
        fw = frac_word(n, m, ea, eb)
        assert cyc(fw) == cyc(fw[::-1])
    print("p, p^mult and the (A^{n/m}B)^m word are reversal symmetric for all certified (n,m,ea,eb)")

    # 5. counts
    assert len(all_words(6, 4)) == 210 and len(all_words(5, 4)) == 126 and len(all_words(6, 3)) == 84
    # 6. PSD testers
    F = Fraction
    assert ldl_pd_exact([[F(2), F(-4, 3)], [F(-4, 3), F(1)]])[0]
    assert not ldl_pd_exact([[F(1), F(2)], [F(2), F(1)]])[0]
    assert psd_exact([[F(1), F(1)], [F(1), F(1)]]) == (True, 1)
    assert psd_exact([[F(0), F(1)], [F(1), F(0)]])[0] is False
    assert psd_exact([[F(1), F(0), F(1)], [F(0), F(0), F(0)], [F(1), F(0), F(1)]]) == (True, 1)
    print("PSD testers OK on small examples")
    print("ALL CORE SELF-TESTS PASSED")


if __name__ == '__main__':
    main()
