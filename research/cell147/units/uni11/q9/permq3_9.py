# GF(9) version of ../permq3.py: permutation of the 7,300 points of E9 = {x4 = -C x0}, C = 8 (card r4c6's E9.map,
# GF(9) element a + 3b = a + b*i with i^2 = -1) induced by g = R^a (+) Y^m: R a generator of SO(A), A = (x0, x3),
# Q_A = -C x0^2 - x3^2 (order 10), Y an elliptic element of SL(2,9) of order 10 acting on V4 = (x1,x2,x5,x6) ~
# X = [[x1, x2], [-x6, x5]] by right (R) or left (L) multiplication. Usage: python3 permq3_9.py a m R|L OUT
import sys
MAP = '/home/user/degree-diameter/research/squads/d14D7-r4/c6/E9.map'
a_, m_, side, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4]
ADD = [[0]*9 for _ in range(9)]; MUL = [[0]*9 for _ in range(9)]
for x in range(9):
    for y in range(9):
        a, b = x % 3, x // 3; c, d = y % 3, y // 3
        ADD[x][y] = (a + c) % 3 + 3*((b + d) % 3)
        MUL[x][y] = (a*c + 2*b*d) % 3 + 3*((a*d + b*c) % 3)
NEG = [0]*9; INV = [0]*9
for x in range(9):
    for y in range(9):
        if ADD[x][y] == 0: NEG[x] = y
        if MUL[x][y] == 1: INV[x] = y
def add(*xs):
    r = 0
    for x in xs: r = ADD[r][x]
    return r
def mul(x, y): return MUL[x][y]
def sub(x, y): return ADD[x][NEG[y]]
C = 8
def QA(x0, x3): return sub(NEG[mul(C, mul(x0, x0))], mul(x3, x3))
I2 = (1, 0, 0, 1)
def mm(P, Q): return (add(mul(P[0], Q[0]), mul(P[1], Q[2])), add(mul(P[0], Q[1]), mul(P[1], Q[3])),
                      add(mul(P[2], Q[0]), mul(P[3], Q[2])), add(mul(P[2], Q[1]), mul(P[3], Q[3])))
def det(P): return sub(mul(P[0], P[3]), mul(P[1], P[2]))
def order(P):
    Q = P
    for o in range(1, 200):
        if Q == I2: return o
        Q = mm(Q, P)
    return -1
def mpow(P, k):
    Q = I2
    for _ in range(k): Q = mm(Q, P)
    return Q
R = None
for u in range(9):
    for v in range(9):
        for w in range(9):
            for z in range(9):
                P = (u, v, w, z)
                if det(P) != 1: continue
                if any(QA(add(mul(u, s), mul(v, t)), add(mul(w, s), mul(z, t))) != QA(s, t) for s, t in ((1, 0), (0, 1), (1, 1), (1, 3))): continue
                if order(P) == 10: R = P; break
            if R: break
        if R: break
    if R: break
Y = None
for t in range(9):
    P = (0, NEG[1], 1, t)          # [[0, -1], [1, t]], det 1
    if order(P) == 10: Y = P; break
Ra, Ym = mpow(R, a_), mpow(Y, m_)
pts = []
for line in open(MAP):
    v = list(map(int, line.split())); pts.append(tuple(v[2:9]))
def norm(y):
    for k in range(7):
        if y[k]:
            iv = INV[y[k]]; return tuple(MUL[iv][t] for t in y)
key = {norm(p): i for i, p in enumerate(pts)}
k11, k12, k21, k22 = Ym
perm = []
for p in pts:
    x0, x1, x2, x3, x4, x5, x6 = p
    y0 = add(mul(Ra[0], x0), mul(Ra[1], x3)); y3 = add(mul(Ra[2], x0), mul(Ra[3], x3)); y4 = NEG[mul(C, y0)]
    if side == 'R':
        y1 = add(mul(x1, k11), mul(x2, k21)); y2 = add(mul(x1, k12), mul(x2, k22))
        y6 = sub(mul(x6, k11), mul(x5, k21)); y5 = sub(mul(x5, k22), mul(x6, k12))
    else:
        y1 = sub(mul(k11, x1), mul(k12, x6)); y2 = add(mul(k11, x2), mul(k12, x5))
        y6 = NEG[sub(mul(k21, x1), mul(k22, x6))]; y5 = add(mul(k21, x2), mul(k22, x5))
    perm.append(key[norm((y0, y1, y2, y3, y4, y5, y6))])
assert sorted(perm) == list(range(len(pts)))
open(out, 'w').write('\n'.join(map(str, perm)) + '\n')
print(f"R={R} Y={Y} a={a_} m={m_} side={side}")
