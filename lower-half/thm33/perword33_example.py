"""Exact (integer / rational) check: the per-word strengthening of Theorem 4 is false, even in sign.

A = diag(1, 10^5, 9*10^5),  B = [[130001, 1400, -100], [1400, 50, 28], [-100, 28, 26]]   (both positive definite)
gives tr(A^2 B A B^2) < 0 < tr((AB)^3), while the averaged (3,3) inequality (Theorem 4) holds with room.
Construction (log): A = diag(eps, y, z) with eps -> 0, B = Gram(u, p, q) + I with p, q at a small angle and
u ~ (p/|p| - q/|q|) long; the word trace then contains |u|^2 <u_hat, H u_hat>, H = y^3 W_y^2 + z^3 W_z^2 +
(yz(y+z)/2)(W_y W_z + W_z W_y), which is indefinite.
Second part: scanning A = diag(eps, 1, 9) over rational eps gives points with |tr(A^2BAB^2)| < tr((AB)^3), i.e. the
integer-exponent instance tr((AB)^3) <= |tr(A^2BAB^2)| of the Ando-Hiai-Okubo question (MIA 3 (2000), (1.7)) fails
too (in line with the known failures of the K = 2 case: Plevnik 2016, Carlen-Lieb 2022)."""
from fractions import Fraction as Fr


def mm(X, Y):
    n = len(X)
    return [[sum(X[i][k] * Y[k][j] for k in range(n)) for j in range(n)] for i in range(n)]


def mpow(X, k):
    R = X
    for _ in range(k - 1):
        R = mm(R, X)
    return R


def tr(X):
    return sum(X[i][i] for i in range(len(X)))


def leading_minors(B):
    b = B
    m1 = b[0][0]
    m2 = b[0][0] * b[1][1] - b[0][1] * b[1][0]
    m3 = (b[0][0] * (b[1][1] * b[2][2] - b[1][2] * b[2][1]) - b[0][1] * (b[1][0] * b[2][2] - b[1][2] * b[2][0])
          + b[0][2] * (b[1][0] * b[2][1] - b[1][1] * b[2][0]))
    return m1, m2, m3


def report(A, B, tag):
    w = tr(mm(mm(mm(mm(mm(A, A), B), A), B), B))          # tr(A^2 B A B^2)
    t3 = tr(mpow(mm(A, B), 3))                              # tr((AB)^3)
    a3b3 = tr(mm(mpow(A, 3), mpow(B, 3)))                   # tr(A^3 B^3)
    f = a3b3 + 2 * w - 3 * t3
    print(f"{tag}: leading minors A {leading_minors(A)}, B {leading_minors(B)}")
    print(f"   tr(A^2BAB^2) = {w}\n   tr((AB)^3)   = {t3}\n   tr(A^3B^3)   = {a3b3}")
    print(f"   Theorem 4 combination tr(A^3B^3) + 2 tr(A^2BAB^2) - 3 tr((AB)^3) = {f}  (> 0: {f > 0})")
    print(f"   per-word gap tr(A^2BAB^2) - tr((AB)^3) = {w - t3}  (< 0: {w - t3 < 0});  "
          f"|tr(A^2BAB^2)| < tr((AB)^3): {abs(w) < t3}")
    return w, t3


B = [[130001, 1400, -100], [1400, 50, 28], [-100, 28, 26]]
A = [[1, 0, 0], [0, 10 ** 5, 0], [0, 0, 9 * 10 ** 5]]
report(A, B, "integer example")

# scan for |tr(A^2BAB^2)| < tr((AB)^3) with A = diag(eps, 1, 9), same B
hits = []
for j in range(1, 200):
    eps = Fr(j, 10 ** 6)
    Ae = [[eps, 0, 0], [0, 1, 0], [0, 0, 9]]
    w = tr(mm(mm(mm(mm(mm(Ae, Ae), B), Ae), B), B))
    t3 = tr(mpow(mm(Ae, B), 3))
    if abs(w) < t3:
        hits.append((eps, w / t3))
print(f"eps in {{j/10^6 : j < 200}} with |tr(A^2BAB^2)| < tr((AB)^3): {len(hits)} values, e.g.")
for eps, r in hits[:3] + hits[-2:]:
    print(f"   eps = {eps}: tr(A^2BAB^2)/tr((AB)^3) = {float(r):+.6f}")
if hits:
    eps = hits[len(hits) // 2][0]
    report([[eps, 0, 0], [0, 1, 0], [0, 0, 9]], B, f"rational example eps = {eps}")
