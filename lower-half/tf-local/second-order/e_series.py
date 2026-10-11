import sympy as sp
x, Y, th, h = sp.symbols('x Y theta h', positive=True)
# a = e^x, b = e^Y (so y = r Y with r = (1-theta)/theta); scale x = h*X1, Y = h*X2
X1, X2 = sp.symbols('X1 X2', positive=True)
r = (1 - th) / th
a = sp.exp(h * X1); b = sp.exp(h * X2)
xx = h * X1; yy = r * h * X2
p, q = a - 1, b - 1
E = th * (xx * yy * (sp.exp(xx + yy) - 1) / (xx + yy) - (sp.exp(xx) - 1) * (sp.exp(yy) - 1)) \
    + th * xx * yy / (xx + yy) * (1 - sp.exp(-th * (xx + yy))) \
    + p * q / (p - q) ** 2 * ((1 - th) * p * ((b / a) ** th - 1) + th * q * ((a / b) ** (1 - th) - 1))
for order in range(2, 7):
    c = sp.simplify(sp.series(E, h, 0, order + 1).removeO().coeff(h, order))
    print(f"h^{order}:", sp.factor(c))
