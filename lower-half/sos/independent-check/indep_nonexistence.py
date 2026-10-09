"""Independent exact check of the non-existence certificates (separating functionals), internal check.

For a functional y on cyclic classes (extended from the listed words to their rotation AND reversal classes; a
reversal-invariant y is a valid functional both for identities modulo rotation and modulo rotation+reversal):
  * y >= 0 on the cone {sum tr(g^*g) + sum tr(X h^*X h) + sum tr(Y l^*Y l)} restricted to the bidegree of f
    <=> every localized moment matrix M_P[u,v] = y(P u^* P v) is PSD (u, v all half-words of the forced bidegree).
    Checked exactly: the nonzero pattern is split into connected components, each component block is tested by
    exact symmetric elimination (zero pivots require zero rows).
  * y(f) < 0 with f rebuilt from the definition (indep_core).
  * Mixed localizer pairs (P != Q in {1,X,Y}) are excluded by parity (reported).
Usage: python -I indep_nonexistence.py [files ...]
"""
import json
import os
import sys
import time
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from indep_core import (cyc, poly_p, poly_pmult, poly_sub, all_words, psd_exact, components,  # noqa: E402
                        frac_word)

sys.set_int_max_str_digits(0)
CERT_DIR = os.path.join(HERE, '..', 'certs')
F = Fraction

# claims hard-coded from SOS_RESULTS.md section 2 (target, cone, value of y(f) stated there)
Y33 = {'AAABBB': F(1), 'AABABB': F(-4, 3), 'ABABAB': F(2)}
Y63 = {'AAAAAABBB': F(1), 'AAAABAABB': F(-4, 3), 'AABAABAAB': F(2)}
IND_AB3 = {'ABABAB': F(1)}
CLAIMS = {
    'nonSOS_F33_pureSOS.json': dict(n=3, m=3, ea=2, eb=2, lhs='p', rhs=[('xxyyxxyyxxyy', 1)], loc=[''], y=IND_AB3, val=F(-9, 10)),
    'nonSOS_F33_QM.json': dict(n=3, m=3, ea=2, eb=2, lhs='p', rhs=[('xxyyxxyyxxyy', 1)], loc=['', 'x', 'y'], y=Y33, val=F(-23, 10)),
    'nonSOS_H33_QM.json': dict(n=3, m=3, ea=2, eb=2, lhs='p', rhs=[('xy' * 6, 1)], loc=['', 'x', 'y'], y=Y33, val=F(-3, 10)),
    'nonSOS_H33_QM_Y4.json': dict(n=3, m=3, ea=2, eb=4, lhs='p', rhs=[('xyy' * 6, 1)], loc=['', 'x', 'y'], y=Y33, val=F(-3, 10)),
    'nonSOS_Q33_QM_X4Y4.json': dict(n=3, m=3, ea=4, eb=4, lhs='p', rhs=[('xy' * 12, 1)], loc=['', 'x', 'y'], y=Y33, val=F(-3, 10)),
    'nonSOS_D33_QM.json': dict(n=3, m=3, ea=2, eb=2, lhs='p', sub='pmult', rhs=[], loc=['', 'x', 'y'], y=IND_AB3, val=F(-11, 90)),
    'nonSOS_M33_QM.json': dict(n=3, m=3, ea=2, eb=2, lhs='pmult', rhs=[('xxyyxxyyxxyy', 1)], loc=['', 'x', 'y'], y=IND_AB3, val=F(-7, 9)),
    'nonSOS_P33_pureSOS.json': dict(n=3, m=3, ea=2, eb=2, lhs='p', rhs=[], loc=[''], y=Y33, val=F(-3, 10)),
    'nonSOS_P33_QM.json': dict(n=3, m=3, ea=2, eb=2, lhs='p', rhs=[], loc=['', 'x', 'y'], y=Y33, val=F(-3, 10)),
    'nonSOS_P33_QM_Y4.json': dict(n=3, m=3, ea=2, eb=4, lhs='p', rhs=[], loc=['', 'x', 'y'], y=Y33, val=F(-3, 10)),
    'nonSOS_P33_QM_X4Y4.json': dict(n=3, m=3, ea=4, eb=4, lhs='p', rhs=[], loc=['', 'x', 'y'], y=Y33, val=F(-3, 10)),
    'nonSOS_P63_QM.json': dict(n=6, m=3, ea=2, eb=2, lhs='p', rhs=[], loc=['', 'x', 'y'], y=Y63, val=F(-3, 28)),
    'nonSOS_F63_QM.json': dict(n=6, m=3, ea=2, eb=2, lhs='p', rhs=[('xxxxyy' * 3, 1)], loc=['', 'x', 'y'], y=Y63, val=F(-59, 28)),
    'nonSOS_S63_QM.json': dict(n=6, m=3, ea=2, eb=2, lhs='p', rhs=[('xxy' * 6, 1)], loc=['', 'x', 'y'], y=Y63, val=F(-3, 28)),
}


def ab_to_xy(w, ea, eb):
    return ''.join('x' * ea if c == 'A' else 'y' * eb for c in w)


def build_target(n, m, ea, eb, lhs, rhs, sub=None):
    f = poly_p(n, m, ea, eb) if lhs == 'p' else poly_pmult(n, m, ea, eb)
    for w, c in rhs:
        f = poly_sub(f, {cyc(w): Fraction(c)})
    if sub == 'pmult':
        f = poly_sub(f, poly_pmult(n, m, ea, eb))
    return f


def functional(ywords):
    """y on cyclic classes from {word: value}; each word's rotation class and reversal class get the value."""
    y = {}
    for w, v in ywords.items():
        for k in (cyc(w), cyc(w[::-1])):
            if k in y and y[k] != v:
                raise ValueError("y not reversal-consistent")
            y[k] = v
    return y


def moment_check(y, f_bideg, P):
    tx, ty = f_bideg
    px, py = 2 * P.count('x'), 2 * P.count('y')
    if (tx - px) % 2 or (ty - py) % 2 or tx < px or ty < py:
        return dict(P=P or '1', size=0, psd=True, note='no half-words (parity)')
    hw = all_words((tx - px) // 2, (ty - py) // 2)
    N = len(hw)
    entries = {}
    for i, u in enumerate(hw):
        left = P + u[::-1] + P
        for j in range(i, N):
            v = y.get(cyc(left + hw[j]), 0)
            if v != 0:
                entries[(i, j)] = v
    # symmetry check on the nonzero pattern (M[u,v] must equal M[v,u])
    for (i, j), v in list(entries.items()):
        if i != j:
            back = y.get(cyc(P + hw[j][::-1] + P + hw[i]), 0)
            assert back == v, "moment matrix not symmetric"
    support = sorted(set(i for ij in entries for i in ij))
    idx = {a: k for k, a in enumerate(support)}
    comps = components(len(support), [(idx[i], idx[j]) for (i, j) in entries if i != j])
    blocks = []
    ok = True
    for comp in comps:
        rows = [support[k] for k in comp]
        Mb = [[entries.get((min(a, b), max(a, b)), Fraction(0)) for b in rows] for a in rows]
        psd, rank = psd_exact(Mb)
        ok = ok and psd
        blocks.append(dict(words=[hw[a] for a in rows], matrix=[[str(x) for x in row] for row in Mb], psd=psd,
                           rank=rank))
    return dict(P=P or '1', size=N, nonzeros=len(entries), n_blocks=len(blocks), psd=ok, blocks=blocks)


def verify(fn, log):
    cl = CLAIMS[fn]
    with open(os.path.join(CERT_DIR, fn)) as fh:
        cert = json.load(fh)
    meta = cert['meta']
    t0 = time.time()
    n, m, ea, eb = cl['n'], cl['m'], cl['ea'], cl['eb']
    f = build_target(n, m, ea, eb, cl['lhs'], cl['rhs'], cl.get('sub'))
    # agreement with the file's meta (my reading)
    fm = build_target(meta['n'], meta['m'], meta['ea'], meta['eb'], meta['lhs'],
                      [(w, c) for c, w in meta['rhs']], meta.get('sub'))
    meta_ok = (fm == f) and sorted(meta['localizers']) == sorted(cl['loc'])
    # functional: from the claim (A,B words) and from the file; they must agree
    y_claim = functional({ab_to_xy(w, ea, eb): v for w, v in cl['y'].items()})
    y_file = functional({w: Fraction(v) for w, v in cert['y'].items()})
    y_ok = (y_claim == y_file)
    k0 = next(iter(f))
    fb = (k0.count('x'), k0.count('y'))
    # parity exclusion of mixed localizer pairs
    mixed = []
    for P, Q in (('', 'x'), ('', 'y'), ('x', 'y')):
        dx = fb[0] - P.count('x') - Q.count('x')
        dy = fb[1] - P.count('y') - Q.count('y')
        mixed.append((P or '1', Q or '1', 'excluded by parity' if (dx % 2 or dy % 2) else 'NOT excluded'))
    res = [moment_check(y_file, fb, P) for P in cl['loc']]
    # also test the full localizer set {1, X, Y} even for 'pure SOS' claims (informative)
    extra = [moment_check(y_file, fb, P) for P in ('', 'x', 'y') if P not in cl['loc']]
    yf = sum((v * y_file.get(k, 0) for k, v in f.items()), Fraction(0))
    psd_all = all(r['psd'] for r in res)
    ok = psd_all and yf < 0 and meta_ok and y_ok
    log(f"== {fn}: target {cl['lhs']}_{{{n},{m}}}(X^{ea},Y^{eb}){' - p^mult' if cl.get('sub') else ''}"
        f"{''.join(' - ' + w for w, _ in cl['rhs'])}; localizers {[p or '1' for p in cl['loc']]}; bidegree {fb}")
    log(f"    meta agrees with the claim: {meta_ok}; functional in file == functional stated in SOS_RESULTS: {y_ok}")
    for r in res + extra:
        tag = '' if r in res else '  [extra localizer, not part of the claim]'
        if r['size'] == 0:
            log(f"    M_{r['P']}: {r['note']}{tag}")
            continue
        bl = '; '.join(f"{b['words']} -> {b['matrix']} psd={b['psd']}" for b in r['blocks'][:4])
        log(f"    M_{r['P']}: {r['size']}x{r['size']}, {r['nonzeros']} nonzero (upper) entries, {r['n_blocks']} nonzero "
            f"blocks, PSD exactly: {r['psd']}{tag}")
        if r['blocks']:
            log(f"        blocks: {bl}{' ...' if len(r['blocks']) > 4 else ''}")
    log(f"    mixed localizer pairs: {mixed}")
    log(f"    y(f) = {yf} (claimed {cl['val']}: {'matches' if yf == cl['val'] else 'DIFFERS'}) -> "
        f"{'NON-EXISTENCE CONFIRMED' if ok else 'NOT CONFIRMED'} ({time.time() - t0:.1f}s)")
    return dict(file=fn, ok=ok, yf=str(yf), claimed=str(cl['val']), yf_matches=(yf == cl['val']), meta_ok=meta_ok,
                y_ok=y_ok, psd=psd_all, sizes=[(r['P'], r['size'], r.get('n_blocks')) for r in res],
                extra_psd=[(r['P'], r['psd']) for r in extra], mixed=mixed)


def main():
    names = sys.argv[1:] or list(CLAIMS)
    logf = open(os.path.join(HERE, 'logs', 'indep_nonexistence.log'), 'a')

    def log(s):
        print(s, flush=True)
        logf.write(s + '\n')
        logf.flush()
    log(f"# run {time.strftime('%Y-%m-%d %H:%M:%S')} files={names}")
    res = [verify(fn, log) for fn in names]
    with open(os.path.join(HERE, 'logs', 'indep_nonexistence.json'), 'w') as fh:
        json.dump(res, fh, indent=1)
    log("SUMMARY: " + ", ".join(f"{r['file']}: {'OK' if r['ok'] else 'FAIL'}" for r in res))


if __name__ == '__main__':
    main()
