"""Negative controls for indep_verify_positive.py: every tampered certificate / wrong claim must be REJECTED."""
import copy
import json
import os
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import indep_verify_positive as V  # noqa: E402
from indep_core import ldl_pd_exact, cyc, poly_p, poly_sub, frac_word  # noqa: E402
from flint import fmpq  # noqa: E402

sys.set_int_max_str_digits(0)


def load(fn):
    with open(os.path.join(V.CERT_DIR, fn)) as fh:
        return json.load(fh)


def check(cert, target):
    """True iff the certificate is accepted for the given target (identity modulo rotation with lambda > 0)."""
    try:
        if cert.get('format') == 'gram':
            s_num, s_den, info = V.sos_gram(cert['blocks'], lambda s: None)
            if s_num is None:
                return False
        else:
            s_num, s_den, info = V.sos_explicit(cert['terms'], lambda s: None)
    except AssertionError:
        return False
    lam, bad, _ = V.ratio_check(target, s_num, s_den)
    return (not bad) and lam is not None and lam > 0


def main():
    logf = open(os.path.join(HERE, 'logs', 'tamper_tests.log'), 'w')

    def log(s):
        print(s, flush=True)
        logf.write(s + '\n')
    results = []

    def expect(name, accepted, should_accept):
        ok = (accepted == should_accept)
        results.append(ok)
        log(f"  {'PASS' if ok else 'PROBLEM'}: {name}: accepted={accepted} (expected {should_accept})")

    f44 = V.claim_target(V.CLAIMS['F44_gram.json'])
    d44 = V.claim_target(V.CLAIMS['D44_11-xx-yy.json'])
    m44 = V.claim_target(V.CLAIMS['M44_11-xx-yy.json'])
    f64 = V.claim_target(V.CLAIMS['F64_11-xx-yy.json'])
    f34 = V.claim_target(V.CLAIMS['F34m_11-xx-yy.json'])

    g = load('F44_gram.json')
    expect("F44_gram untouched vs (F) target", check(g, f44), True)
    expect("F44_gram data vs (D) (4,4) target", check(g, d44), False)
    expect("F44_gram data vs (M) (4,4) target", check(g, m44), False)
    # stronger RHS: p - (1 + 1/1000) tr(AB)^4
    stronger = poly_sub(poly_p(4, 4, 2, 2), {cyc(frac_word(4, 4, 2, 2)): Fraction(1001, 1000)})
    expect("F44_gram data vs p - 1.001 tr(AB)^4", check(g, stronger), False)
    t = copy.deepcopy(g)
    a = Fraction(t['blocks'][0]['S'][0][1]) + Fraction(1, 10 ** 6)
    t['blocks'][0]['S'][0][1] = str(a)
    t['blocks'][0]['S'][1][0] = str(a)
    expect("F44_gram with one off-diagonal S entry changed by 1e-6 (symmetric)", check(t, f44), False)
    t = copy.deepcopy(g)
    col = t['blocks'][2]['T_columns'][0]
    i = next(k for k, v in enumerate(col) if v != '0')
    col[i] = str(int(col[i]) + 1)
    expect("F44_gram with one integer T entry changed in an (X,X) block", check(t, f44), False)
    t = copy.deepcopy(g)
    t['blocks'][4]['P'] = 'x'
    t['blocks'][4]['Q'] = 'x'
    expect("F44_gram with a (Y,Y) block relabelled as (X,X)", check(t, f44), False)
    t = copy.deepcopy(g)
    w = t['blocks'][0]['words']
    w[3], w[4] = w[4], w[3]
    expect("F44_gram with two half-word labels swapped", check(t, f44), False)

    e = load('F44_11-xx-yy.json')
    expect("F44 explicit untouched", check(e, f44), True)
    t = copy.deepcopy(e)
    k0 = next(iter(t['terms'][5]['poly']))
    t['terms'][5]['poly'][k0] = str(-Fraction(t['terms'][5]['poly'][k0]))
    expect("F44 explicit with one coefficient sign-flipped", check(t, f44), False)
    t = copy.deepcopy(e)
    t['terms'][7]['weight'] = str(-Fraction(t['terms'][7]['weight']))
    expect("F44 explicit with one weight negated", check(t, f44), False)
    t = copy.deepcopy(e)
    del t['terms'][-1]
    expect("F44 explicit with the last square dropped", check(t, f44), False)

    c34 = load('F34m_11-xx-yy.json')
    c64 = load('F64_11-xx-yy.json')
    expect("F34m data vs its own target", check(c34, f34), True)
    expect("F34m data vs the (6,4) target (same bidegree and RHS word)", check(c34, f64), False)
    expect("F64 data vs the (3,4) target", check(c64, f34), False)

    # exact PD tester on a genuinely indefinite perturbation of a real S block
    S = [[Fraction(v) for v in row] for row in c64['blocks'][0]['S']]
    Sq = [[fmpq(x.numerator, x.denominator) for x in row] for row in S]
    pd, piv = ldl_pd_exact(Sq)
    r = len(S)
    Sq2 = [row[:] for row in Sq]
    Sq2[r - 1][r - 1] = Sq2[r - 1][r - 1] - piv[-1] - fmpq(1, 10 ** 9)   # last pivot becomes -1e-9
    pd2, piv2 = ldl_pd_exact(Sq2)
    results.append(pd and not pd2)
    log(f"  {'PASS' if (pd and not pd2) else 'PROBLEM'}: exact LDL^T: F64 block 0 PD={pd}; after lowering the last "
        f"diagonal entry by (last pivot + 1e-9): PD={pd2} (last pivot = {float(piv2[-1]):.3e})")
    Sq3 = [row[:] for row in Sq]
    Sq3[r - 1][r - 1] = Sq3[r - 1][r - 1] - piv[-1] + fmpq(1, 10 ** 30)     # last pivot becomes +1e-30
    pd3, piv3 = ldl_pd_exact(Sq3)
    results.append(pd3)
    log(f"  {'PASS' if pd3 else 'PROBLEM'}: exact LDL^T: lowering by (last pivot - 1e-30) keeps PD={pd3} "
        f"(last pivot = {float(piv3[-1]):.3e}), i.e. the test resolves 1e-30 exactly")
    log(f"ALL NEGATIVE CONTROLS BEHAVE AS EXPECTED: {all(results)}  ({sum(results)}/{len(results)})")


if __name__ == '__main__':
    main()
