"""Rigorous form of the symbolic checks: closed-form polynomial vectors are verified directly against the defining
linear equations (polynomial identities with integer coefficients, hence valid over every field of odd
characteristic), so no step depends on generic pivots.

Chart A (p5 != 0): p0 = 1 - c p4, p1 = (p3^2 - p0 p4 - p2 p6)/p5;  z = (s p5, -1/p5 - s p2).
"""
import sympy as sp

c, s, t = sp.symbols('c s t')
p2, p3, p4, p5, p6 = sp.symbols('p2 p3 p4 p5 p6')
PAIRS = [((1, 2), (3, 4)), ((5, 4), (3, 2)), ((2, 0), (3, 5)), ((6, 5), (3, 0)), ((0, 1), (3, 6)), ((4, 6), (3, 1))]


def eqs(x, y):
    """the 7 bilinear conditions 'y is H(q)-collinear with x' (Tits + polar)"""
    pl = lambda i, j: x[i] * y[j] - x[j] * y[i]
    out = [pl(i, j) - pl(k, l) for (i, j), (k, l) in PAIRS]
    out.append(x[0] * y[4] + x[4] * y[0] + x[1] * y[5] + x[5] * y[1] + x[2] * y[6] + x[6] * y[2] - 2 * x[3] * y[3])
    return out


p0 = 1 - c * p4
p1 = (p3**2 - p0 * p4 - p2 * p6) / p5
p = [p0, p1, p2, p3, p4, p5, p6]
alpha, beta = s * p5, -1 / p5 - s * p2
X = [-c * p5 * (c * p2**2 * p4 * p5 * s + c * p2 * p4 - p2**2 * p5 * s - p2 + p3 * p5 + p4 * p5**3 * s),
     c**2 * p2**2 * p4**2 * p5 * s + c**2 * p2 * p4**2 - c * p2**3 * p5 * p6 * s + c * p2**2 * p3**2 * p5 * s
     - c * p2**2 * p4 * p5 * s - c * p2**2 * p6 + c * p2 * p3**2 - c * p2 * p4 + c * p4**2 * p5**3 * s
     + p2 * p3 * p5**2 * s - p2 * p5**3 * p6 * s + p3**2 * p5**3 * s + p3 * p5 - p5**2 * p6,
     p5 * (c * p2**2 + p5**2) * (p2 * p5 * s + 1),
     p5 * (c * p2**2 * p3 * p5 * s + c * p2 * p3 - c * p4 * p5 + p2 * p5**2 * s + p3 * p5**3 * s + p5),
     p5 * (c * p2**2 * p4 * p5 * s + c * p2 * p4 - p2**2 * p5 * s - p2 + p3 * p5 + p4 * p5**3 * s),
     p5**3 * s * (c * p2**2 + p5**2),
     p5 * (c**2 * p4**2 + c * p2**2 * p5 * p6 * s - c * p2 * p4 * p5 * s + c * p3**2 - 2 * c * p4 + p2 * p5 * s
           + p3 * p5**2 * s + p5**3 * p6 * s + 1)]
print('Q(p) =', sp.cancel(p[0] * p[4] + p[1] * p[5] + p[2] * p[6] - p[3]**2))
print('X collinear with p:', [sp.cancel(e) for e in eqs(p, X)])
print('L(X) =', sp.expand(X[0] + c * X[4]), '  alpha X2 + beta X5 =', sp.cancel(alpha * X[2] + beta * X[5]))
D = c * X[2]**2 + X[5]**2
print('D(X) factorisation:', sp.factor(D))
Psi = sp.cancel((X[2] * X[3] - X[4] * X[5]) / D + beta**3 / (alpha**2 + c * beta**2))
target = -(p2**3 * p5 * s + p2**2 - p2 * p3 * p5 + p4 * p5**2) / (p5 * (c * p2**2 + p5**2))
print('Psi - closed form =', sp.cancel(Psi - target))
