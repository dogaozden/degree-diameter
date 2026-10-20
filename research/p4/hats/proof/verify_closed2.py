"""Closed-form checks for chart B (p5 = 0) of the key identity and for the constancy of nu on S-lines.
Each closed form is found by a generic computation and then verified directly against the defining equations
(polynomial identities with integer coefficients, valid in every odd characteristic)."""
import sympy as sp

c, s, t = sp.symbols('c s t')
PAIRS = [((1, 2), (3, 4)), ((5, 4), (3, 2)), ((2, 0), (3, 5)), ((6, 5), (3, 0)), ((0, 1), (3, 6)), ((4, 6), (3, 1))]


def eqs(x, y):
    pl = lambda i, j: x[i] * y[j] - x[j] * y[i]
    out = [pl(i, j) - pl(k, l) for (i, j), (k, l) in PAIRS]
    out.append(x[0] * y[4] + x[4] * y[0] + x[1] * y[5] + x[5] * y[1] + x[2] * y[6] + x[6] * y[2] - 2 * x[3] * y[3])
    return out


def mat(x):
    ys = sp.symbols('y0:7')
    return sp.Matrix([[sp.diff(e, yy) for yy in ys] for e in eqs(x, ys)])


def poly_vec(v):
    v = [sp.cancel(t_) for t_ in v]
    den = sp.lcm([sp.denom(sp.together(t_)) for t_ in v])
    w = [sp.factor(sp.cancel(t_ * den)) for t_ in v]
    g = sp.gcd([t_ for t_ in w if t_ != 0])
    return [sp.factor(sp.cancel(t_ / g)) for t_ in w]


def solve_point(x, extra_rows):
    A = sp.Matrix.vstack(mat(x), *[sp.Matrix([r]) for r in extra_rows]).applyfunc(sp.cancel)
    return [poly_vec(list(v)) for v in A.nullspace(simplify=True)]


def nu(X):
    return sp.cancel((X[2] * X[3] - X[4] * X[5]) / (c * X[2]**2 + X[5]**2))


# chart B
p1, p2, p3, p4 = sp.symbols('p1 p2 p3 p4')
p0 = 1 - c * p4
p6 = (p3**2 - p0 * p4) / p2
p = [p0, p1, p2, p3, p4, 0, p6]
alpha, beta = -1 / p2, s
[X] = solve_point(p, [[1, 0, 0, 0, c, 0, 0], [0, 0, alpha, 0, 0, beta, 0]])
print('B: X =', X)
print('B: Q(p) =', sp.cancel(p[0] * p[4] + p[2] * p[6] - p[3]**2), ' collinear:', set(sp.cancel(e) for e in eqs(p, X)),
      ' L(X) =', sp.cancel(X[0] + c * X[4]), ' z-eq =', sp.cancel(alpha * X[2] + beta * X[5]))
print('B: D(X) =', sp.factor(c * X[2]**2 + X[5]**2))
Psi = sp.cancel(nu(X) + beta**3 / (alpha**2 + c * beta**2))
print('B: Psi =', sp.factor(Psi), '  slope per step (0,-p2) minus target:',
      sp.cancel(sp.diff(Psi, s) * (-p2) + p2**3 / (c * p2**2)))

# nu on S-lines: X in Pi on Q (chart X5 != 0), second point Y of pi_X cap Pi
X2, X3, X4, X5, X6 = sp.symbols('X2 X3 X4 X5 X6')
Xa = [-c * X4, (X3**2 + c * X4**2 - X2 * X6) / X5, X2, X3, X4, X5, X6]
sol = solve_point(Xa, [[1, 0, 0, 0, c, 0, 0]])
Xn = poly_vec(Xa)
Y = next(v for v in sol if sp.Matrix(v).rank(simplify=True) and sp.Matrix([Xn, v]).rank(simplify=True) == 2)
print('S-line: Y =', Y)
print('S-line: Y collinear with X:', set(sp.cancel(e) for e in eqs(Xa, Y)), ' L(Y) =', sp.cancel(Y[0] + c * Y[4]),
      ' Q(Y) =', sp.cancel(Y[0] * Y[4] + Y[1] * Y[5] + Y[2] * Y[6] - Y[3]**2))
Z = [sp.cancel(a_ + t * b_) for a_, b_ in zip(Xa, Y)]
print('S-line: nu(X + tY) - nu(X) =', sp.cancel(nu(Z) - nu(Xa)), ';  nu(Y) - nu(X) =', sp.cancel(nu(Y) - nu(Xa)))
# chart X5 = 0, X2 != 0
X1 = sp.symbols('X1')
Xb = [-c * X4, X1, X2, X3, X4, 0, (X3**2 + c * X4**2) / X2]
sol = solve_point(Xb, [[1, 0, 0, 0, c, 0, 0]])
Xbn = poly_vec(Xb)
Y = next(v for v in sol if sp.Matrix([Xbn, v]).rank(simplify=True) == 2)
Z = [sp.cancel(a_ + t * b_) for a_, b_ in zip(Xb, Y)]
print('S-line (X5=0): collinear', set(sp.cancel(e) for e in eqs(Xb, Y)), ' L(Y) =', sp.cancel(Y[0] + c * Y[4]),
      ' nu(X+tY) - nu(X) =', sp.cancel(nu(Z) - nu(Xb)), ' nu(Y) - nu(X) =', sp.cancel(nu(Y) - nu(Xb)))
