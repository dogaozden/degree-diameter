"""Symbolic check of the key identity behind the explicit whisker rule.

Model: Q(x) = x0x4 + x1x5 + x2x6 - x3^2, H(q)-lines through p span the plane pi_p = {y : M_p y = 0} (Tits' six
equations p12=p34, p54=p32, p20=p35, p65=p30, p01=p36, p46=p31 with p_ij = x_i y_j - x_j y_i, plus B(x,y) = 0).
L = x0 + c x4,  nu(x) = (x2x3 - x4x5)/(c x2^2 + x5^2).
Claim: for p on Q with L(p) = 1 and z = (alpha, beta) on the line alpha p2 + beta p5 = -1, let X(z) be the point of
pi_p with L(X) = 0 and alpha X2 + beta X5 = 0. Then
    Psi(z) = nu(X(z)) + beta^3 / (alpha^2 + c beta^2)
is affine along that line, with slope -p2^3/(c p2^2 + p5^2) per step (p5, -p2).
We work over the rational function field Q(c, p2, p3, p4, p5, p6, s) with p0 = 1 - c p4 and p1 solved from Q(p) = 0,
so the identity holds over every field of characteristic != 2 where the denominators are nonzero.
"""
import sympy as sp

c, p2, p3, p4, p5, p6, s = sp.symbols('c p2 p3 p4 p5 p6 s')
p0 = 1 - c * p4
p1 = (p3**2 - p0 * p4 - p2 * p6) / p5
x = [p0, p1, p2, p3, p4, p5, p6]
PAIRS = [((1, 2), (3, 4)), ((5, 4), (3, 2)), ((2, 0), (3, 5)), ((6, 5), (3, 0)), ((0, 1), (3, 6)), ((4, 6), (3, 1))]
M = sp.zeros(7, 7)
for r, ((i, j), (k, l)) in enumerate(PAIRS):
    M[r, j] += x[i]; M[r, i] -= x[j]; M[r, l] -= x[k]; M[r, k] += x[l]
M[6, :] = sp.Matrix([[x[4], x[5], x[6], -2 * x[3], x[0], x[1], x[2]]])
M = M.applyfunc(sp.together)
ns = M.nullspace(simplify=True)
print('dim pi_p =', len(ns))
U = [sp.Matrix(v_).applyfunc(sp.cancel) for v_ in ns]
alpha = s * p5
beta = -1 / p5 - s * p2
Lrow = [1, 0, 0, 0, c, 0, 0]
Zrow = [0, 0, alpha, 0, 0, beta, 0]
A = sp.Matrix([[sum(Lrow[i] * u[i] for i in range(7)) for u in U],
               [sum(Zrow[i] * u[i] for i in range(7)) for u in U]]).applyfunc(sp.cancel)
coef = A.nullspace(simplify=True)
assert len(coef) == 1
a = coef[0]
X = sum((a[k] * U[k] for k in range(len(U))), sp.zeros(7, 1)).applyfunc(sp.cancel)
I = X[2] * X[3] - X[4] * X[5]
D = c * X[2]**2 + X[5]**2
Psi = sp.cancel(I / D + beta**3 / (alpha**2 + c * beta**2))
d2 = sp.cancel(sp.diff(Psi, s, 2))
slope = sp.cancel(sp.diff(Psi, s))
target = -p2**3 / (c * p2**2 + p5**2)
print('second derivative in s:', d2)
print('slope - target:', sp.cancel(slope - target))
# sanity: X is on Q, in Pi and in Pi_z, collinear with p
print('Q(X) =', sp.cancel(X[0] * X[4] + X[1] * X[5] + X[2] * X[6] - X[3]**2))

# a polynomial representative of X(z): clear denominators
den = sp.lcm([sp.denom(sp.together(t)) for t in X])
Xp = (X * den).applyfunc(lambda t: sp.factor(sp.cancel(t)))
g = sp.gcd([t for t in Xp if t != 0])
Xp = Xp.applyfunc(lambda t: sp.factor(sp.cancel(t / g)))
print('X(z) proportional to:')
for i, t in enumerate(Xp):
    print('  X%d =' % i, t)
print('nu(X) =', sp.factor(sp.cancel(I / D)))
print('Psi =', sp.factor(Psi))
