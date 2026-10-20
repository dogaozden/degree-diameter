"""Hand-proof ingredients for the char-2 key identity (mod 2, with lambda(p) = a p2 + b p5 = 1 imposed by solving
for a, b in terms of gamma = lambda(J p)): coordinates of X = gamma p + J p, den(X), a^2+ab+d b^2, num(X)."""
import sympy as sp
import proof_J as T
d, g = T.d, sp.symbols('g')
x = T.x
p2, p5 = x[2], x[4]
Th = d * p2**2 + p2 * p5 + p5**2
al = (d * p2 + g * p5) / Th
be = (g * p2 + p2 + p5) / Th
GENS = T.GENS + (g,)
def P2(e):
    n, _ = sp.fraction(sp.together(sp.expand(e)))
    return sp.Poly(sp.expand(n), *GENS, modulus=2)
sub = {T.a: al, T.b: be}
print('lambda(p) = 1:', P2((al * p2 + be * p5 - 1)).is_zero, '; lambda(Jp) = g:', P2(T.lam(T.full(T.J(x))).subs(sub) - g).is_zero)
p = [e.subs(sub) for e in T.full(x)]
Jp = [e.subs(sub) for e in T.full(T.J(x))]
X = [g * pi + ji for pi, ji in zip(p, Jp)]
for i in (2, 3, 4, 5):
    print(f'X{i} =', P2(X[i] * 1).as_expr() if i in (2, 5) else sp.simplify(X[i]))
G2 = g**2 + g + d
print('den(X) = (g^2+g+d) Theta:', P2(T.den(X) - G2 * Th).is_zero)
print('a^2 + ab + d b^2 = (g^2+g+d)/Theta:', P2(al**2 + al * be + d * be**2 - G2 / Th).is_zero)
nump = p[2] * p[3] + p[2] * p[4] + p[4] * p[5]
R = sp.symbols('R')
rest = sp.together(T.num(X) - G2 * nump)
print('num(X) - (g^2+g+d)(p2p3+p2p4+p4p5) = beta *', sp.factor(P2(sp.cancel(rest / be)).as_expr()))
print('beta^3 Theta^2 = beta (g p2 + p2 + p5)^2:', P2(be**3 * Th**2 - be * (g * p2 + p2 + p5)**2).is_zero)
Rv = sp.cancel(rest / be)
tot = sp.cancel(Rv + (g * p2 + p2 + p5)**2 * Th / Th)
print('R =', P2(Rv).as_expr())
for cand_name, cand in [('(g^2+g+d) p2^2 Theta', G2 * p2**2 * Th), ('(g^2+g+d) p2^2', G2 * p2**2)]:
    print('R + (g p2 + p2 + p5)^2 Theta =', cand_name, ':', P2(Rv + (g * p2 + p2 + p5)**2 * Th - cand).is_zero,
          ';  R + (g p2+p2+p5)^2 =', cand_name, ':', P2(Rv + (g * p2 + p2 + p5)**2 - cand).is_zero)
for nm, cand in [('(g+d+1)p2^2 + p5^2', (g + d + 1) * p2**2 + p5**2), ('g p2 p5 + (d+1) p2^2 + p5^2 ...', None)]:
    if cand is None: continue
    print('num(X) = (g^2+g+d)(p2p3+p2p4+p4p5) + beta*(' + nm + '):', P2(T.num(X) - G2 * nump - be * cand).is_zero)
