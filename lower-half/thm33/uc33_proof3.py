import sympy as sp, pickle
x = sp.symbols('x', positive=True)     # x = p^2 > 5
c0 = 80 * x * (x**3 - 8 * x**2 + 50 * x - 100)
c2 = 40 * (7 * x**3 + 85 * x**2 - 290 * x + 400)
c1sq = 1600 * x * (x**3 - 86 * x**2 + 320 * x - 400)**2       # c1^2 (c1 = -40 p (...), p^2 = x)
D = sp.expand(4 * c0 * c2 - c1sq)
print("4 c0 c2 - c1^2 =", sp.factor(D))
Dr = sp.Poly(sp.expand(D / (1600 * x)), x)
print("reduced:", Dr.as_expr())
print("real roots of reduced poly:", [sp.N(r) for r in sp.real_roots(Dr)])
# shift x = 5 + y and check coefficient signs
Ds = sp.Poly(sp.expand(Dr.as_expr().subs(x, 5 + sp.Symbol('y'))), sp.Symbol('y'))
print("in y = x - 5:", Ds.as_expr())
cub = x**3 - 8 * x**2 + 50 * x - 100
print("cubic x^3-8x^2+50x-100 at x=5+y:", sp.expand(cub.subs(x, 5 + sp.Symbol('y'))))
print("7x^3+85x^2-290x+400 at x=5+y:", sp.expand((7 * x**3 + 85 * x**2 - 290 * x + 400).subs(x, 5 + sp.Symbol('y'))))
print("x^3-86x^2+320x-400 roots:", [sp.N(r) for r in sp.real_roots(sp.Poly(x**3 - 86 * x**2 + 320 * x - 400, x))])
