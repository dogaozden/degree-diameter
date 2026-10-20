"""Characteristic 2: the complex structure J_z on Pi_z and the key identity, as polynomial identities mod 2.

Pi_z : X3 = X0 + d X4 + a X2 + b X5 (Tr(d) = 1, so t^2 + t + d is irreducible).  Coordinates of Pi_z:
x = (x0, x1, x2, x4, x5, x6), X3 eliminated.  Q = X0X4 + X1X5 + X2X6 + X3^2, polar form B (no X3 term).
J_z (found by linear algebra on H(8), then checked here for symbolic d, a, b):
    x0' = (d+1) x0 + d a x2 + d^2 x4 + (a + d b) x5
    x1' = b x0 + x1 + a b x2 + (a + d b) x4 + b^2 x5 + x6
    x2' = x2 + x5
    x4' = x0 + (a + b) x2 + d x4 + b x5
    x5' = d x2
    x6' = (a + b) x0 + d x1 + a^2 x2 + d a x4 + a b x5
Checks (all mod 2, as polynomials in d, a, b, x, y):
 (a) J^2 + J + d = 0;  Q(Jx) = d Q(x);  B(x, Jx) = Q(x)
 (b) the six Tits differences of x ^ Jx are Q(x) times constants
 (c) nu-num and nu-den on Pi (z = 0) scale by d under J_0 and their polar forms with (x, J_0 x) are num, den
 (d) key identity: for a point p (Q(p) = 0) with lambda(p) := p3 + p0 + d p4 = 1 in Pi_z,
     X = gamma p + J p (gamma = lambda(J p)) lies in Pi, and
     nu(X) + b^3/(a^2 + a b + d b^2) = (p2 p3 + p2 p4 + p4 p5 + b p2^2) / (d p2^2 + p2 p5 + p5^2).
"""
import sympy as sp

d, a, b = sp.symbols('d a b')
x = sp.symbols('x0 x1 x2 x4 x5 x6')
y = sp.symbols('y0 y1 y2 y4 y5 y6')
GENS = (d, a, b) + x + y


def P2(e):
    num, den = sp.fraction(sp.together(sp.expand(e)))
    return sp.Poly(sp.expand(num), *GENS, modulus=2)


def zero(e):
    return P2(e).is_zero


def full(v):
    """6 coordinates of Pi_z -> 7 coordinates X0..X6"""
    v0, v1, v2, v4, v5, v6 = v
    return [v0, v1, v2, v0 + d * v4 + a * v2 + b * v5, v4, v5, v6]


def J(v):
    v0, v1, v2, v4, v5, v6 = v
    return [(d + 1) * v0 + d * a * v2 + d ** 2 * v4 + (a + d * b) * v5,
            b * v0 + v1 + a * b * v2 + (a + d * b) * v4 + b ** 2 * v5 + v6,
            v2 + v5,
            v0 + (a + b) * v2 + d * v4 + b * v5,
            d * v2,
            (a + b) * v0 + d * v1 + a ** 2 * v2 + d * a * v4 + a * b * v5]


def Q(V):
    return V[0] * V[4] + V[1] * V[5] + V[2] * V[6] + V[3] ** 2


def B(V, W):
    return V[0] * W[4] + V[4] * W[0] + V[1] * W[5] + V[5] * W[1] + V[2] * W[6] + V[6] * W[2]


PAIRS = [((1, 2), (3, 4)), ((5, 4), (3, 2)), ((2, 0), (3, 5)), ((6, 5), (3, 0)), ((0, 1), (3, 6)), ((4, 6), (3, 1))]

X, JX = full(x), full(J(x))
JJ = J(J(x))
print('(a) J^2 + J + d = 0:', all(zero(JJ[i] + J(x)[i] + d * x[i]) for i in range(6)))
print('    Q(Jx) = d Q(x):', zero(Q(JX) - d * Q(X)), '  B(x, Jx) = Q(x):', zero(B(X, JX) - Q(X)))
cons = []
for (i, j), (k, l) in PAIRS:
    diff = X[i] * JX[j] - X[j] * JX[i] - (X[k] * JX[l] - X[l] * JX[k])
    qt, r = sp.div(P2(diff), P2(Q(X)))
    cons.append((r.is_zero, qt.as_expr()))
print('(b) Tits differences of x^Jx are Q(x) times:', [c for ok, c in cons], 'exact division:', all(ok for ok, c in cons))
# (c) on Pi (a = b = 0)
sub0 = {a: 0, b: 0}
X0v, J0v = [e.subs(sub0) for e in full(x)], [e.subs(sub0) for e in full(J(x))]
num = lambda V: V[2] * V[3] + V[2] * V[4] + V[4] * V[5]
den = lambda V: d * V[2] ** 2 + V[2] * V[5] + V[5] ** 2
Y0v = [e.subs(sub0) for e in full(y)]
pol = lambda f, V, W: f([vi + wi for vi, wi in zip(V, W)]) - f(V) - f(W)
print('(c) num(J0 x) = d num(x):', zero(num(J0v) - d * num(X0v)), '  den(J0 x) = d den(x):', zero(den(J0v) - d * den(X0v)))
print('    polar num(x, J0x) = num(x):', zero(pol(num, X0v, J0v) - num(X0v)),
      '  polar den(x, J0x) = den(x):', zero(pol(den, X0v, J0v) - den(X0v)))
# so on the line <x, J0 x>: num(s x + t J0 x) = (s^2 + s t + d t^2) num(x), same for den  -> nu constant on S-lines
s_, t_ = sp.symbols('s t')
lin = [s_ * xi + t_ * ji for xi, ji in zip(X0v, J0v)]
GENS = GENS + (s_, t_)
nrm = s_ ** 2 + s_ * t_ + d * t_ ** 2
print('    num(s x + t J0 x) = N(s,t) num(x):', zero(num(lin) - nrm * num(X0v)), '  den likewise:', zero(den(lin) - nrm * den(X0v)))
# (d) key identity. p in Pi_z with coordinates x (so p3 = x0 + d x4 + a x2 + b x5); lambda(p) = p3 + p0 + d p4 = a p2 + b p5 := 1
p = full(x)
lam = lambda V: V[3] + V[0] + d * V[4]
Jp = full(J(x))
gamma = lam(Jp)
Xz = [gamma * pi + ji for pi, ji in zip(p, Jp)]
print('(d) lambda(J p) = gamma =', P2(gamma).as_expr(), ';  lambda(X) = gamma (lambda(p) + 1), so X in Pi when lambda(p) = 1:',
      zero(lam(Xz) - gamma * (lam(p) + 1)))
# impose a p2 + b p5 = 1: chart p5 != 0 -> b = (1 + a p2)/p5 ; Q(p) = 0 -> x1 = (x0 x4 + x2 x6 + p3^2)/x5
p2, p5 = x[2], x[4]
subs = {b: (1 + a * p2) / p5}
subsQ = {x[1]: (x[0] * x[3] + x[2] * x[5] + p[3] ** 2) / x[4]}
lhs = num(Xz) / den(Xz) + b ** 3 / (a ** 2 + a * b + d * b ** 2)
rhs = (p[2] * p[3] + p[2] * p[4] + p[4] * p[5] + b * p[2] ** 2) / (d * p[2] ** 2 + p[2] * p[5] + p[5] ** 2)
diff = (lhs - rhs).subs(subsQ).subs(subs)
print('    nu(X) + b^3/(a^2+ab+db^2) = (p2p3 + p2p4 + p4p5 + b p2^2)/(d p2^2 + p2p5 + p5^2)  [chart p5 != 0]:', zero(diff))
subs2 = {a: 1 / p2, p5: 0}
diff2 = (lhs - rhs).subs({x[4]: 0}).subs({a: (1 + b * 0) / p2})
subsQ2 = {x[5]: (x[0] * x[3] + p[3].subs({x[4]: 0}) ** 2) / x[2]}
print('    same identity [chart p5 = 0]:', zero(diff2.subs(subsQ2)))
print('    den(X) =', sp.factor(P2(den(Xz)).as_expr()))
