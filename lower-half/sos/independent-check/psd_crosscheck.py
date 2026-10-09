"""Second, independent exact PD test of every Gram block S (cross-check of the LDL^T in indep_verify_positive.py):
Sylvester's criterion with flint's exact determinant of every leading principal minor (S scaled to an integer
matrix by the lcm of its denominators; scaling by a positive constant does not change signs).  Also reports
floating-point eigenvalues (numpy, informational only: min eigenvalue and condition number)."""
import json
import os
import sys
import time
from fractions import Fraction
from math import lcm

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from flint import fmpz_mat  # noqa: E402

sys.set_int_max_str_digits(0)
CERT_DIR = os.path.join(HERE, '..', 'certs')
FILES = ['F44_gram.json', 'D44_11-xx-yy.json', 'M44_11-xx-yy.json', 'F34m_11-xx-yy.json', 'D34m_11-xx-yy.json',
         'M34m_11-xx-yy.json', 'F64_11-xx-yy.json']


def main():
    logf = open(os.path.join(HERE, 'logs', 'psd_crosscheck.log'), 'w')

    def log(s):
        print(s, flush=True)
        logf.write(s + '\n')
        logf.flush()
    allok = True
    for fn in FILES:
        with open(os.path.join(CERT_DIR, fn)) as fh:
            cert = json.load(fh)
        for bi, blk in enumerate(cert['blocks']):
            t0 = time.time()
            S = [[Fraction(v) for v in row] for row in blk['S']]
            r = len(S)
            D = 1
            for row in S:
                for x in row:
                    D = lcm(D, x.denominator)
            Si = [[x.numerator * (D // x.denominator) for x in row] for row in S]
            ok = True
            min_digits = None
            for k in range(1, r + 1):
                dk = fmpz_mat(k, k, [Si[i][j] for i in range(k) for j in range(k)]).det()
                if not dk > 0:
                    ok = False
                    break
                nd = len(str(abs(int(dk))))
                min_digits = nd if min_digits is None else min(min_digits, nd)
            Sf = np.array([[float(x) for x in row] for row in S])
            ev = np.linalg.eigvalsh(Sf)
            allok = allok and ok
            log(f"{fn} block {bi} (P=Q={blk['P'] or '1'}, r={r}): all {r} leading principal minors > 0 (exact): {ok}; "
                f"float eigenvalues min {ev[0]:.3e}, max {ev[-1]:.3e}, cond {ev[-1] / ev[0]:.2e} ({time.time() - t0:.1f}s)")
    log(f"ALL GRAM BLOCKS PD BY SYLVESTER (exact): {allok}")


if __name__ == '__main__':
    main()
