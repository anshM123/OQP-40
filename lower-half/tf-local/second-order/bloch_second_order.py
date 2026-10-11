"""Check the 2x2 second-order formula
   d^2/de^2 <Pi_{A,B(e)}, F> at e = 0  =  -2 (a1-a2)(b1-b2) int_0^1 F_ab(P(u)) du,   P(u) = P2 + u (P1 - P2),
for A = diag(a1,a2), B(e) = R_e diag(b1,b2) R_e^T, using the exact Bloch-sphere formula
   <Pi, F> = 2 E_n [(1 + r d/dr) F(a0 + r a.n, b0 + r b.n)]_{r=1}   (n uniform on S^2),
and smooth test functions F = cos(xa + yb), F = (a b)^{1.7}."""
import mpmath as mp
mp.mp.dps = 30

def pi_pair(F, dF, a1, a2, b1, b2, e):
    a0, az = (a1 + a2) / 2, (a1 - a2) / 2
    b0, bz = (b1 + b2) / 2, (b1 - b2) / 2
    c2, s2 = mp.cos(2 * e), mp.sin(2 * e)
    # integrand depends on n = (sin p cos c, sin p sin c, cos p): a.n = az n_z, b.n = bz (c2 n_z + s2 n_x)
    def f(p, c):
        nz, nx = mp.cos(p), mp.sin(p) * mp.cos(c)
        da, db = az * nz, bz * (c2 * nz + s2 * nx)
        a, b = a0 + da, b0 + db
        Fa, Fb = dF(a, b)
        return (F(a, b) + Fa * da + Fb * db) * mp.sin(p)
    return 2 * mp.quad(f, [0, mp.pi / 2, mp.pi], [0, mp.pi, 2 * mp.pi]) / (4 * mp.pi)

def check(F, dF, Fab, a1, a2, b1, b2, label):
    e = mp.mpf('1e-4')
    v0 = pi_pair(F, dF, a1, a2, b1, b2, 0)
    vp = pi_pair(F, dF, a1, a2, b1, b2, e)
    vm = pi_pair(F, dF, a1, a2, b1, b2, -e)
    num = (vp - 2 * v0 + vm) / e ** 2
    pred = -2 * (a1 - a2) * (b1 - b2) * mp.quad(lambda u: Fab(a2 + u * (a1 - a2), b2 + u * (b1 - b2)), [0, 1])
    print(f"{label}: numeric {mp.nstr(num, 10)}  formula {mp.nstr(pred, 10)}")

a1, a2, b1, b2 = mp.mpf('2.3'), mp.mpf('0.7'), mp.mpf('0.5'), mp.mpf('1.9')
x, y = mp.mpf('0.8'), mp.mpf('-1.3')
F1 = lambda a, b: mp.cos(x * a + y * b)
dF1 = lambda a, b: (-x * mp.sin(x * a + y * b), -y * mp.sin(x * a + y * b))
F1ab = lambda a, b: -x * y * mp.cos(x * a + y * b)
check(F1, dF1, F1ab, a1, a2, b1, b2, 'cos(xa+yb)')
k = mp.mpf('1.7')
F2 = lambda a, b: (a * b) ** k
dF2 = lambda a, b: (k * a ** (k - 1) * b ** k, k * a ** k * b ** (k - 1))
F2ab = lambda a, b: k * k * (a * b) ** (k - 1)
check(F2, dF2, F2ab, a1, a2, b1, b2, '(ab)^1.7')
# The TF kernel (only C^{1,1}) needs a stable second difference: see bloch_kernel_check.py.
