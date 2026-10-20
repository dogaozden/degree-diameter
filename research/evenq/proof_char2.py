"""Symbolic proof of the key identity in characteristic 2 (all even q).

Setting: Q = X0X4 + X1X5 + X2X6 + X3^2,  Pi: X3 + X0 + d X4 = 0,  Pi_z: X3 + X0 + d X4 + a X2 + b X5 = 0.
p a free point, normalised L0(p) = p3 + p0 + d p4 = 1.  For z on A_p, X(z) = the point with pX an H(q)-line, X in Pi,
X in Pi_z.  Claim: Phi_p(z) = nu(X(z)) + b^3/(a^2 + ab + d b^2) is affine along A_p with increment
p2^3/(d p2^2 + p2 p5 + p5^2) per step (p5, p2), where nu(X) = (X2X3 + X2X4 + X4X5)/(d X2^2 + X2X5 + X5^2).

Method: work in Z[d, s, p...]; a kernel vector of six of the linear conditions is given by signed 6x6 minors (a
polynomial identity over Z, hence mod 2).  We then check, as polynomial identities mod 2 (valid over every field of
characteristic 2): all seven collinearity conditions with p (Tits' six equations and the polar form), Q(X) = 0, X in
Pi and Pi_z, the factorisation of d X2^2 + X2X5 + X5^2, and the identity for Phi_p.
Two charts: p5 != 0 (z = (s p5, 1/p5 + s p2)) and p5 = 0, p2 != 0 (z = (1/p2, s)).
"""
import itertools

import sympy as sp

d, s = sp.symbols('d s')
p0, p1s, p2, p4, p5, p6 = sp.symbols('p0 p1 p2 p4 p5 p6')
PAIRS = [((1, 2), (3, 4)), ((5, 4), (3, 2)), ((2, 0), (3, 5)), ((6, 5), (3, 0)), ((0, 1), (3, 6)), ((4, 6), (3, 1))]
GENS = (d, s, p0, p1s, p2, p4, p5, p6)


def m2(e):
    """numerator of e as a polynomial mod 2"""
    num, _ = sp.fraction(sp.together(sp.expand(e)))
    return sp.Poly(sp.expand(num), *GENS, modulus=2)


def zero2(e):
    return m2(e).is_zero


def rows(x):
    """the 7 linear conditions on y: Tits' six (p_ij = p_kl) and the polar form (char 2: no X3 term)"""
    out = []
    for (i, j), (k, l) in PAIRS:
        r = [0] * 7
        r[j] += x[i]; r[i] -= x[j]; r[l] -= x[k]; r[k] += x[l]
        out.append(r)
    out.append([x[4], x[5], x[6], 0, x[0], x[1], x[2]])
    return out


def kernel(M):
    """signed maximal minors of a 6x7 matrix: a vector annihilated by every row (identity over Z)"""
    Mm = sp.Matrix(M)
    return [(-1) ** j * Mm[:, [c for c in range(7) if c != j]].det(method='berkowitz') for j in range(7)]


def chart(name, p, al, be, pclear, inc):
    print(f'--- chart {name}', flush=True)
    R = [[sp.expand(pclear * c) for c in r] for r in rows(p)]
    Pi = [1, 0, 0, 1, d, 0, 0]
    Pz = [0, 0, sp.expand(pclear * al), 0, 0, sp.expand(pclear * be), 0]
    for combo in itertools.combinations(range(7), 4):
        X = kernel([R[i] for i in combo] + [Pi, Pz])
        X2 = [m2(x) for x in X]
        if any(not x.is_zero for x in X2):
            break
    # divide by the gcd mod 2
    g = X2[0]
    for x in X2[1:]:
        g = g.gcd(x)
    X2 = [x.quo(g) for x in X2]
    print('rows used', combo, '; common factor removed:', g.as_expr(), flush=True)
    Xe = [x.as_expr() for x in X2]
    ok = all(zero2(sum(c * y for c, y in zip(r, Xe))) for r in rows(p))
    print('X collinear with p (Tits + polar), mod 2:', ok)
    print('Q(X) = 0 mod 2:', zero2(Xe[0] * Xe[4] + Xe[1] * Xe[5] + Xe[2] * Xe[6] + Xe[3] ** 2))
    print('X in Pi:', zero2(Xe[3] + Xe[0] + d * Xe[4]), '  X in Pi_z:', zero2(al * Xe[2] + be * Xe[5]))
    Nx = d * Xe[2] ** 2 + Xe[2] * Xe[5] + Xe[5] ** 2
    for i in range(7):
        print(f'X{i} =', m2(Xe[i]).as_expr())
    nu = (Xe[2] * Xe[3] + Xe[2] * Xe[4] + Xe[4] * Xe[5]) / Nx
    Phi = nu + be ** 3 / (al ** 2 + al * be + d * be ** 2)
    Phi0 = Phi.subs(s, 0)
    print(f'Phi(s) - Phi(0) - s * ({inc}) = 0 mod 2:', zero2(Phi - Phi0 - s * inc), flush=True)
    num, den = sp.fraction(sp.together(Phi0))
    print('Phi(0) = num/den with num =', m2(num).as_expr(), ' den =', m2(den).as_expr())
    return Xe


# chart p5 != 0: p3 from the normalisation, p1 from Q(p) = 0
p3 = 1 + p0 + d * p4
p1 = (p0 * p4 + p2 * p6 + p3 ** 2) / p5
p = [p0, p1, p2, p3, p4, p5, p6]
chart('p5 != 0', p, s * p5, 1 / p5 + s * p2, p5, p2 ** 3 / (d * p2 ** 2 + p2 * p5 + p5 ** 2))
# chart p5 = 0, p2 != 0: p6 from Q(p) = 0, p1 free
p6b = (p0 * p4 + p3 ** 2) / p2
pb = [p0, p1s, p2, p3, p4, 0, p6b]
chart('p5 = 0', pb, 1 / p2, s, p2, 1 / d)  # step (0, 1) = (p5, p2)/p2: increment (p2^3/(d p2^2))/p2
