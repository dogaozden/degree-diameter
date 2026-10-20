"""Remaining symbolic checks for the whisker theorem (see identity.py).
(S2) the identity in the chart p5 = 0, p2 != 0;
(S3) nu is constant on every line of H(q) inside Pi = {x0 + c x4 = 0} that avoids v = <e1, e6>;
(S1') direct check of the closed form of X(z) from identity.py: M_p X = 0, L(X) = 0, alpha X2 + beta X5 = 0.
"""
import sympy as sp

c, s, t = sp.symbols('c s t')
PAIRS = [((1, 2), (3, 4)), ((5, 4), (3, 2)), ((2, 0), (3, 5)), ((6, 5), (3, 0)), ((0, 1), (3, 6)), ((4, 6), (3, 1))]


def tits(x):
    M = sp.zeros(7, 7)
    for r, ((i, j), (k, l)) in enumerate(PAIRS):
        M[r, j] += x[i]; M[r, i] -= x[j]; M[r, l] -= x[k]; M[r, k] += x[l]
    M[6, :] = sp.Matrix([[x[4], x[5], x[6], -2 * x[3], x[0], x[1], x[2]]])
    return M.applyfunc(sp.together)


def nu(X):
    return sp.cancel((X[2] * X[3] - X[4] * X[5]) / (c * X[2]**2 + X[5]**2))


def point_on(M_rows, extra):
    A = sp.Matrix.vstack(M_rows, *[sp.Matrix([r]) for r in extra]).applyfunc(sp.cancel)
    ns = A.nullspace(simplify=True)
    return [sp.Matrix(v).applyfunc(sp.cancel) for v in ns]


# (S2): chart p5 = 0
p1, p2, p3, p4 = sp.symbols('p1 p2 p3 p4')
p0 = 1 - c * p4
p6 = (p3**2 - p0 * p4) / p2          # Q(p) = p0 p4 + p2 p6 - p3^2 = 0 with p5 = 0
x = [p0, p1, p2, p3, p4, 0, p6]
alpha = -1 / p2                       # alpha p2 + beta p5 = -1
beta = s                              # direction (p5, -p2) = (0, -p2): beta moves by -p2 per step
U = point_on(tits(x), [])
assert len(U) == 3
A = sp.Matrix([[sum(r[i] * u[i] for i in range(7)) for u in U] for r in
               ([1, 0, 0, 0, c, 0, 0], [0, 0, alpha, 0, 0, beta, 0])]).applyfunc(sp.cancel)
co = A.nullspace(simplify=True)
assert len(co) == 1
X = sum((co[0][k] * U[k] for k in range(3)), sp.zeros(7, 1)).applyfunc(sp.cancel)
Psi = sp.cancel(nu(X) + beta**3 / (alpha**2 + c * beta**2))
print('(S2) d^2 Psi / d beta^2 =', sp.cancel(sp.diff(Psi, s, 2)))
# slope per step (p5, -p2) = (0, -p2): d Psi / d beta * (-p2); target -p2^3/(c p2^2)
print('(S2) slope - target =', sp.cancel(sp.diff(Psi, s) * (-p2) - (-p2**3 / (c * p2**2))))

# (S3): nu constant on H(q)-lines inside Pi. X in Pi on Q: X0 = -c X4; chart X5 != 0 solves X1.
X2, X3, X4, X5, X6 = sp.symbols('X2 X3 X4 X5 X6')
X1 = (X3**2 + c * X4**2 - X2 * X6) / X5
Xv = [-c * X4, X1, X2, X3, X4, X5, X6]
U = point_on(tits(Xv), [[1, 0, 0, 0, c, 0, 0]])
print('(S3) dim (pi_X cap Pi) =', len(U))
Y = (U[0] + t * U[1]).applyfunc(sp.cancel)
print('(S3) d nu(line point) / dt =', sp.cancel(sp.diff(nu(Y), t)))
# chart X5 = 0 (then X2 != 0 off v): solve X6
X1s = sp.symbols('X1')
X6b = (X3**2 + c * X4**2) / X2
Xw = [-c * X4, X1s, X2, X3, X4, 0, X6b]
U = point_on(tits(Xw), [[1, 0, 0, 0, c, 0, 0]])
Y = (U[0] + t * U[1]).applyfunc(sp.cancel)
print('(S3, X5=0) dim =', len(U), ' d nu / dt =', sp.cancel(sp.diff(nu(Y), t)))
