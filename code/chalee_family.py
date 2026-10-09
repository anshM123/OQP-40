"""Cha-Lee family (arXiv:2603.19927, Sec. II):
    A_x = [[1,0,0],[0,x,-x],[0,-x,x]],   B_x = [[x,-x,0],[-x,x,0],[0,0,1]],  x >= 0.
High-precision (mpmath) evaluation of:
  - p_{n,m}(A_x,B_x)  (word average),
  - the OQP 40 lower bound  L = tr exp(n log A + m log B)  (A_x, B_x regularised by + delta*I, delta -> 0),
  - the doubling comparison  p_{2n,2m}(A,B)  vs  p_{n,m}(A^2,B^2),
  - Dinh's pinched bound  Tr(A^n E_A(B)^m)."""
from math import comb

import mpmath as mp

mp.mp.dps = 60


def mat(rows):
    return mp.matrix(rows)


def A_(x):
    return mat([[1, 0, 0], [0, x, -x], [0, -x, x]])


def B_(x):
    return mat([[x, -x, 0], [-x, x, 0], [0, 0, 1]])


def word_average(A, B, n, m):
    d = A.rows
    coeffs = [mp.eye(d)]
    for _ in range(n + m):
        new = [mp.zeros(d, d) for _ in range(len(coeffs) + 1)]
        for j, C in enumerate(coeffs):
            new[j] += C * A
            new[j + 1] += C * B
        coeffs = new
    tr = sum(coeffs[m][i, i] for i in range(d))
    return tr / comb(n + m, n)


def herm_fun(M, f):
    E, Q = mp.eighe(M) if hasattr(mp, "eighe") else mp.eigsy(M)
    D = mp.diag([f(e) for e in E])
    return Q * D * Q.T


def lower_bound(A, B, n, m, delta):
    d = A.rows
    LA = herm_fun(A + delta * mp.eye(d), mp.log)
    LB = herm_fun(B + delta * mp.eye(d), mp.log)
    X = n * LA + m * LB
    E, Q = mp.eigsy(X)
    return sum(mp.e ** e for e in E)


def pinched(A, B, n, m):
    E, Q = mp.eigsy(A)
    Bq = Q.T * B * Q
    # group equal eigenvalues of A (tolerance relative to 1e-40)
    idx = sorted(range(A.rows), key=lambda i: E[i])
    groups, cur = [], [idx[0]]
    for i in idx[1:]:
        if abs(E[i] - E[cur[-1]]) < mp.mpf(10) ** (-40):
            cur.append(i)
        else:
            groups.append(cur)
            cur = [i]
    groups.append(cur)
    tot = mp.mpf(0)
    for g in groups:
        sub = mp.matrix([[Bq[i, j] for j in g] for i in g])
        ev, _ = mp.eigsy(sub)
        tot += E[g[0]] ** n * sum(e ** m for e in ev)
    return tot


for x in [mp.mpf("0.1"), mp.mpf("0.01"), mp.mpf("0.001")]:
    A, B = A_(x), B_(x)
    for n, m in [(3, 3), (5, 5), (6, 6), (5, 7)]:
        p = word_average(A, B, n, m)
        L0 = lower_bound(A, B, n, m, mp.mpf(10) ** (-30))
        L1 = lower_bound(A, B, n, m, mp.mpf(10) ** (-20))
        pin = pinched(A, B, n, m)
        print(f"x={mp.nstr(x, 3)} (n,m)=({n},{m}): p={mp.nstr(p, 10)}  L(1e-30)={mp.nstr(L0, 10)}  "
              f"L(1e-20)={mp.nstr(L1, 10)}  p/L={mp.nstr(p / L0, 8)}  pinched={mp.nstr(pin, 10)}  "
              f"tr A^nB^m={mp.nstr(sum((A ** n * B ** m)[i, i] for i in range(3)), 10)}", flush=True)
    for n, m in [(1, 1), (2, 2), (3, 3), (5, 5)]:
        p2 = word_average(A, B, 2 * n, 2 * m)
        q = word_average(A * A, B * B, n, m)
        print(f"   doubling x={mp.nstr(x, 3)} (n,m)=({n},{m}): p_2n,2m(A,B)={mp.nstr(p2, 10)}  "
              f"p_n,m(A^2,B^2)={mp.nstr(q, 10)}  ratio={mp.nstr(p2 / q, 8)}", flush=True)
