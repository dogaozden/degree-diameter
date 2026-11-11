"""Symbolic check of Lemma 5.6 (a),(b),(d) (odd q, over Z[x,alpha,beta,c]) and Lemma 5.11 (a),(b),(d)
(even q, over F_2[delta,alpha,beta,x]) exactly as printed."""
import sympy as sp
x1, x2, x3, x4, x5, x6, al, be, c = sp.symbols('x1 x2 x3 x4 x5 x6 alpha beta c')
X = [x1, x2, x3, x4, x5, x6]
def J(v):
    v1, v2, v3, v4, v5, v6 = v
    return [-be*v3 + al*v4 - v6, v5, -c*v4 - be*v5, v3 + be*v2, -c*v2, c*v1 + al*be*v2 + al*v3 + c*be*v4 + be**2*v5]
def Qz(v):
    v1, v2, v3, v4, v5, v6 = v
    return v1*v5 + v2*v6 - v3**2 - c*v4**2 - al*v2*v4 - be*v4*v5
def lift(v):  # 7 coordinates X0..X6 with X0 = -c x4 - alpha x2 - beta x5
    v1, v2, v3, v4, v5, v6 = v
    return [-c*v4 - al*v2 - be*v5, v1, v2, v3, v4, v5, v6]
JX = J(X); JJX = J(JX)
ok_a1 = all(sp.expand(JJX[i] + c*X[i]) == 0 for i in range(6))
ok_a2 = sp.expand(Qz(JX) - c*Qz(X)) == 0
bz = sp.expand(Qz([a + b for a, b in zip(X, JX)]) - Qz(X) - Qz(JX))
ok_a3 = bz == 0
# also check Q(lift(x)) == Q_z(x)
Q7 = lambda V: V[0]*V[4] + V[1]*V[5] + V[2]*V[6] - V[3]**2
ok_lift = sp.expand(Q7(lift(X)) - Qz(X)) == 0
U, V = lift(X), lift(JX)
p = lambda i, j: U[i]*V[j] - U[j]*V[i]
diffs = [p(1,2)-p(3,4), p(5,4)-p(3,2), p(2,0)-p(3,5), p(6,5)-p(3,0), p(0,1)-p(3,6), p(4,6)-p(3,1)]
expect = [1, 0, 0, -c, al, -be]
ok_b = [sp.expand(d - e*Qz(X)) == 0 for d, e in zip(diffs, expect)]
# what the differences actually are, if not
actual = [sp.factor(sp.expand(d)) for d in diffs]
# (d) on Pi (z=0): num = y2 y3 - y4 y5, den = c y2^2 + y5^2 with s x + t J0 x
s, t = sp.symbols('s t')
J0 = lambda v: [ee.subs({al: 0, be: 0}) for ee in J(v)]
Y = [s*a + t*b for a, b in zip(X, J0(X))]
num = lambda y: y[1]*y[2] - y[3]*y[4]; den = lambda y: c*y[1]**2 + y[4]**2
ok_d = (sp.expand(num(Y) - (s**2 + c*t**2)*num(X)) == 0, sp.expand(den(Y) - (s**2 + c*t**2)*den(X)) == 0)
print("Lemma 5.6 odd: J^2=-c:", ok_a1, " Q_z(Jx)=cQ_z(x):", ok_a2, " b_z(x,Jx)=0:", ok_a3, " Q(lift)=Q_z:", ok_lift)
print("   (b) differences equal Q_z(x)*(1,0,0,-c,alpha,-beta):", ok_b)
if not all(ok_b):
    print("   actual differences / Q_z:", [sp.simplify(a/sp.factor(Qz(X))) if a != 0 else 0 for a in actual])
print("   (d) num and den scale by s^2+c t^2:", ok_d)

# ---------- even q ----------
x0, dl = sp.symbols('x0 delta')
Xe = [x0, x1, x2, x4, x5, x6]
def Je(v):
    v0, v1, v2, v4, v5, v6 = v
    return [(dl + 1)*v0 + dl*al*v2 + dl**2*v4 + (al + dl*be)*v5,
            be*v0 + v1 + al*be*v2 + (al + dl*be)*v4 + be**2*v5 + v6,
            v2 + v5,
            v0 + (al + be)*v2 + dl*v4 + be*v5,
            dl*v2,
            (al + be)*v0 + dl*v1 + al**2*v2 + dl*al*v4 + al*be*v5]
def lifte(v):
    v0, v1, v2, v4, v5, v6 = v
    return [v0, v1, v2, v0 + dl*v4 + al*v2 + be*v5, v4, v5, v6]
Qe = lambda V: V[0]*V[4] + V[1]*V[5] + V[2]*V[6] + V[3]**2
be7 = lambda U, V: U[0]*V[4] + U[4]*V[0] + U[1]*V[5] + U[5]*V[1] + U[2]*V[6] + U[6]*V[2]
def mod2(e):
    P = sp.Poly(sp.expand(e), *(Xe + [al, be, dl, s, t]))
    return all(int(cf) % 2 == 0 for cf in P.coeffs())
JXe = Je(Xe); JJXe = Je(JXe)
ok1 = all(mod2(JJXe[i] + JXe[i] + dl*Xe[i]) for i in range(6))
U, V = lifte(Xe), lifte(JXe)
ok2 = mod2(Qe(V) - dl*Qe(U)); ok3 = mod2(be7(U, V) - Qe(U))
pe = lambda i, j: U[i]*V[j] - U[j]*V[i]
diffs = [pe(1,2)-pe(3,4), pe(5,4)-pe(3,2), pe(2,0)-pe(3,5), pe(6,5)-pe(3,0), pe(0,1)-pe(3,6), pe(4,6)-pe(3,1)]
expect = [1, 0, 0, dl, al, be]
okb = [mod2(d - e*Qe(U)) for d, e in zip(diffs, expect)]
J0e = lambda v: [ee.subs({al: 0, be: 0}) for ee in Je(v)]
Ye = [s*a + t*b for a, b in zip(Xe, J0e(Xe))]
L0 = lambda v: lifte(v)  # with alpha=beta=0 substituted below
def numden(v):
    W = [w.subs({al: 0, be: 0}) for w in lifte(v)]
    return W[2]*W[3] + W[2]*W[4] + W[4]*W[5], dl*W[2]**2 + W[2]*W[5] + W[5]**2
nY, dY = numden(Ye); nX, dX = numden(Xe)
okd = (mod2(nY - (s**2 + s*t + dl*t**2)*nX), mod2(dY - (s**2 + s*t + dl*t**2)*dX))
print("Lemma 5.11 even: J^2+J+delta=0:", ok1, " Q(Jx)=delta Q(x):", ok2, " b(x,Jx)=Q(x):", ok3)
print("   (b) differences equal Q(x)*(1,0,0,delta,alpha,beta) mod 2:", okb)
print("   (d) num, den scale by s^2+st+delta t^2 mod 2:", okd)
