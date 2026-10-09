import pickle, sympy as sp
p, q, u, v = sp.symbols('p q u v', positive=True)
d = pickle.load(open("uc33_conditions.pkl", "rb"))
for k in ("I", "II", "III"):
    num, den = d[k]
    print(f"--- {k}: numerator =", sp.factor(num))
    # substitute q = p + v (v >= 0): coefficients as polynomials in p
    P = sp.Poly(sp.expand(num.subs(q, p + v)), v)
    print("   in v (q = p + v), coefficients (as polynomials in p):")
    for (deg,), c in zip(P.monoms(), P.coeffs()):
        print(f"     v^{deg}: {sp.factor(c)}")
