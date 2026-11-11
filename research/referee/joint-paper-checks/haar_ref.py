"""Referee check of the connection sets printed in Section 8: (7,5) S4 x Z24, (9,5) Heisenberg mod 11,
Example 8.5 (7,8) PSL(2,19) x Z14 with its automorphism alpha. Diameter = max eccentricity of (e,A), (e,B)
(Theorem 8.4); the graph is also written out for the all-pairs checker for the two D=5 graphs."""
from collections import deque
import itertools
def ecc(elems_mul, e, S, inv):
    # BFS on G x {A,B}: (g,A)~(sg,B); (h,B)~(s^-1 h,A)
    Sinv = [inv(s) for s in S]
    out = []
    for start in [(e, 0), (e, 1)]:
        dist = {start: 0}; dq = deque([start])
        while dq:
            g, side = dq.popleft(); d = dist[(g, side)]
            nb = [(elems_mul(s, g), 1) for s in S] if side == 0 else [(elems_mul(si, g), 0) for si in Sinv]
            for w in nb:
                if w not in dist: dist[w] = d + 1; dq.append(w)
        out.append((len(dist), max(dist.values())))
    return out
# ---- (7,5): S4 x Z24
def perm_from_cycles(cyc):
    p = list(range(4))
    for c in cyc:
        for i in range(len(c)): p[c[i]] = c[(i + 1) % len(c)]
    return tuple(p)
comp = lambda f, h: tuple(f[h[x]] for x in range(4))
pinv = lambda f: tuple(sorted(range(4), key=lambda x: f[x]))
S75 = [((), 0), (((0, 1), (2, 3)), 23), (((0, 3, 2),), 0), (((0, 2),), 18), (((0, 1, 2, 3),), 18), (((1, 2, 3),), 17), (((1, 2),), 3)]
S75 = [(perm_from_cycles(c), x) for c, x in S75]
mul75 = lambda a, b: (comp(a[0], b[0]), (a[1] + b[1]) % 24)
inv75 = lambda a: (pinv(a[0]), (-a[1]) % 24)
r = ecc(mul75, (tuple(range(4)), 0), S75, inv75)
print("(7,5) S4xZ24:", "reached", [x[0] for x in r], "of", 2 * 576, "ecc", [x[1] for x in r])
# ---- (9,5): Heisenberg mod 11
p = 11
S95 = [(0,0,0),(8,6,10),(7,9,3),(10,1,8),(4,4,5),(5,5,8),(6,5,4),(1,0,9),(6,10,8)]
mul95 = lambda x, y: ((x[0]+y[0]) % p, (x[1]+y[1]) % p, (x[2]+y[2]+x[0]*y[1]) % p)
inv95 = lambda x: ((-x[0]) % p, (-x[1]) % p, (-x[2] + x[0]*x[1]) % p)
assert all(mul95(s, inv95(s)) == (0,0,0) for s in S95)
r = ecc(mul95, (0,0,0), S95, inv95)
print("(9,5) Heis(11):", "reached", [x[0] for x in r], "of", 2 * 1331, "ecc", [x[1] for x in r])
# ---- (7,8): PSL(2,19) x Z14
p = 19
def mnorm(M):
    a, b, c, d = [x % p for x in M]
    # representative modulo +-I: make first non-zero entry <= p//2
    for x in (a, b, c, d):
        if x:
            if x > p // 2: a, b, c, d = (-a) % p, (-b) % p, (-c) % p, (-d) % p
            break
    return (a, b, c, d)
mm = lambda X, Y: mnorm((X[0]*Y[0]+X[1]*Y[2], X[0]*Y[1]+X[1]*Y[3], X[2]*Y[0]+X[3]*Y[2], X[2]*Y[1]+X[3]*Y[3]))
minv = lambda X: mnorm((X[3], -X[1], -X[2], X[0]))
S78 = [((1,0,0,1),0), ((2,13,14,6),6), ((4,13,7,4),12), ((2,7,7,6),10), ((6,2,8,6),1), ((6,13,15,1),9), ((1,4,12,11),11)]
for (M, z) in S78: assert (M[0]*M[3] - M[1]*M[2]) % p == 1, M
S78 = [(mnorm(M), z) for M, z in S78]
mul78 = lambda a, b: (mm(a[0], b[0]), (a[1] + b[1]) % 14)
inv78 = lambda a: (minv(a[0]), (-a[1]) % 14)
r = ecc(mul78, ((1,0,0,1), 0), S78, inv78)
print("(7,8) PSL(2,19)xZ14:", "reached", [x[0] for x in r], "of", 2 * 3420 * 14, "ecc", [x[1] for x in r])
g = mnorm((1,3,6,0)); gi = minv(g)
assert (1*0 - 3*6) % p == 1
o = 1; x = g
while x != mnorm((1,0,0,1)): x = mm(x, g); o += 1
alpha = lambda s: (mm(mm(g, s[0]), gi), (9 * s[1]) % 14)
img = [alpha(s) for s in S78]
print("   order of g in PSL(2,19):", o, "; alpha(s_i) = s_j map:", [S78.index(t) if t in S78 else None for t in img])
