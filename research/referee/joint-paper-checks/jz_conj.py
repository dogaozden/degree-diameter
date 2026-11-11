"""Is J_z (Lemma 5.6 / 5.12) the conjugate of J_0 by a collineation of Fact 2.3 carrying Pi to Pi_z?
g = (v,a,w) -> (A v, a, A^{-T} w) with A^{-1} = [[1,0,alpha],[-beta/c,1,0],[0,0,1]] (odd q), [[1,0,alpha],[beta/delta,1,0],[0,0,1]] (even q)."""
import sympy as sp
al, be, c, dl = sp.symbols('alpha beta c delta')
x = sp.symbols('x0:7')
def run(odd=True):
    if odd:
        Ainv = sp.Matrix([[1, 0, al], [-be/c, 1, 0], [0, 0, 1]])
    else:
        Ainv = sp.Matrix([[1, 0, al], [be/dl, 1, 0], [0, 0, 1]])   # Pi_z: X3 = X0 + delta X4 + alpha X2 + beta X5
    A = Ainv.inv(); AiT = Ainv.T
    g = sp.diag(A, sp.Matrix([[1]]), AiT)          # acts on (X0..X6)
    gi = g.inv()
    X = sp.Matrix(x)
    # J_0 on Pi_0 in full coordinates: lift Pi coordinates, apply printed J_0, lift back
    if odd:
        def J0full(Xv):
            x1, x2, x3, x4, x5, x6 = [Xv[i] for i in range(1, 7)]
            y = [-x6, x5, -c*x4, x3, -c*x2, c*x1]
            return sp.Matrix([-c*y[3]] + y)
        def Jzfull(Xv):
            x1, x2, x3, x4, x5, x6 = [Xv[i] for i in range(1, 7)]
            y = [-be*x3 + al*x4 - x6, x5, -c*x4 - be*x5, x3 + be*x2, -c*x2, c*x1 + al*be*x2 + al*x3 + c*be*x4 + be**2*x5]
            return sp.Matrix([-c*y[3] - al*y[1] - be*y[4]] + y)
        onPiz = {x[0]: -c*x[4] - al*x[2] - be*x[5]}
    else:
        def J0full(Xv):
            x0, x1, x2, x4, x5, x6 = Xv[0], Xv[1], Xv[2], Xv[4], Xv[5], Xv[6]
            y = [(dl+1)*x0 + dl**2*x4, x1 + x6, x2 + x5, x0 + dl*x4, dl*x2, dl*x1]
            return sp.Matrix([y[0], y[1], y[2], y[0] + dl*y[3], y[3], y[4], y[5]])
        def Jzfull(Xv):
            x0, x1, x2, x4, x5, x6 = Xv[0], Xv[1], Xv[2], Xv[4], Xv[5], Xv[6]
            y = [(dl+1)*x0 + dl*al*x2 + dl**2*x4 + (al+dl*be)*x5, be*x0 + x1 + al*be*x2 + (al+dl*be)*x4 + be**2*x5 + x6,
                 x2 + x5, x0 + (al+be)*x2 + dl*x4 + be*x5, dl*x2, (al+be)*x0 + dl*x1 + al**2*x2 + dl*al*x4 + al*be*x5]
            return sp.Matrix([y[0], y[1], y[2], y[0] + dl*y[3] + al*y[2] + be*y[4], y[3], y[4], y[5]])
        onPiz = {x[3]: x[0] + dl*x[4] + al*x[2] + be*x[5]}
    Xz = X.subs(onPiz)
    # check g maps Pi_0 onto Pi_z: take a point of Pi_0, map, test equation of Pi_z
    lhs = gi * Xz
    conj = g * J0full(lhs)
    diff = (conj - Jzfull(Xz)).applyfunc(sp.simplify)
    if odd:
        return diff
    else:
        # reduce mod 2
        out = []
        for e in diff:
            num, den = sp.fraction(sp.together(sp.expand(e)))
            P = sp.Poly(sp.expand(num), *x, al, be, dl)
            out.append(all(int(cf) % 2 == 0 for cf in P.coeffs()))
        return out
print("odd q: g J_0 g^-1 - J_z on Pi_z =", list(run(True)))
print("even q: g J_0 g^-1 = J_z mod 2 on Pi_z:", run(False))
# check that g_z maps Pi_0 onto Pi_z (odd q): image of a point of Pi_0 satisfies the equation of Pi_z
Ainv = sp.Matrix([[1, 0, al], [-be/c, 1, 0], [0, 0, 1]]); g = sp.diag(Ainv.inv(), sp.Matrix([[1]]), Ainv.T)
X0 = sp.Matrix([-c*x[4]] + list(x[1:]))   # a point of Pi_0: X0 = -c X4
Y = g * X0
print("odd q: g_z(Pi_0) in Pi_z:", sp.simplify(Y[0] + c*Y[4] + al*Y[2] + be*Y[5]) == 0)
Ainv = sp.Matrix([[1, 0, al], [be/dl, 1, 0], [0, 0, 1]]); g = sp.diag(Ainv.inv(), sp.Matrix([[1]]), Ainv.T)
X0 = sp.Matrix([x[0], x[1], x[2], x[0] + dl*x[4], x[4], x[5], x[6]])
Y = g * X0
e = sp.together(sp.expand(Y[3] - (Y[0] + dl*Y[4] + al*Y[2] + be*Y[5])))
num, den = sp.fraction(e)
print("even q: g_z(Pi_0) in Pi_z (mod 2):", all(int(cf) % 2 == 0 for cf in sp.Poly(sp.expand(num), *x, al, be, dl).coeffs()))
