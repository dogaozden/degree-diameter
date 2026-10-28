# Haar graphs printed in Section 8 of joint.tex: diameter from BFS at (e,A) and (e,B) (Theorem 8.4).
from collections import deque
def haar_diam(elems, mul, invf, S, e):
    def ecc(start_side):
        dist = {(e, start_side): 0}; dq = deque([(e, start_side)])
        while dq:
            g, side = dq.popleft()
            nb = [(mul(s, g), 'B') for s in S] if side == 'A' else [(mul(invf(s), g), 'A') for s in S]
            for v in nb:
                if v not in dist: dist[v] = dist[(g, side)] + 1; dq.append(v)
        assert len(dist) == 2 * len(elems)
        return max(dist.values())
    return max(ecc('A'), ecc('B'))
# (7,5): S4 x Z24; permutations in cycle notation -> one-line tuples; (f o h)(i) = f(h(i))
import itertools
def cyc(*cs):
    p = list(range(4))
    for c in cs:
        for a, b in zip(c, c[1:] + c[:1]): p[a] = b
    return tuple(p)
S4 = list(itertools.permutations(range(4)))
G1 = [(f, x) for f in S4 for x in range(24)]
mul1 = lambda a, b: (tuple(a[0][b[0][i]] for i in range(4)), (a[1] + b[1]) % 24)
def inv1(a):
    f = [0]*4
    for i in range(4): f[a[0][i]] = i
    return (tuple(f), (-a[1]) % 24)
S1 = [(cyc(), 0), (cyc((0,1),(2,3)), 23), (cyc((0,3,2)), 0), (cyc((0,2)), 18), (cyc((0,1,2,3)), 18), (cyc((1,2,3)), 17), (cyc((1,2)), 3)]
print("(7,5):", 2*len(G1), "vertices, diameter", haar_diam(G1, mul1, inv1, S1, (cyc(), 0)))
# (9,5): Heisenberg mod 11
G2 = [(a, b, c) for a in range(11) for b in range(11) for c in range(11)]
mul2 = lambda x, y: ((x[0]+y[0]) % 11, (x[1]+y[1]) % 11, (x[2]+y[2]+x[0]*y[1]) % 11)
inv2 = lambda x: ((-x[0]) % 11, (-x[1]) % 11, (-x[2] + x[0]*x[1]) % 11)
S2 = [(0,0,0),(8,6,10),(7,9,3),(10,1,8),(4,4,5),(5,5,8),(6,5,4),(1,0,9),(6,10,8)]
assert all(mul2(x, inv2(x)) == (0,0,0) for x in G2)
print("(9,5):", 2*len(G2), "vertices, diameter", haar_diam(G2, mul2, inv2, S2, (0,0,0)))
# Example 8.5: PSL(2,19) x Z14
p = 19
def canon(m):
    a, b, c, d = m
    for x in (a, b, c, d):
        if x % p:
            if x % p > p // 2: return tuple((-y) % p for y in m)
            return tuple(y % p for y in m)
SL = [(a, b, c, d) for a in range(p) for b in range(p) for c in range(p) for d in range(p) if (a*d - b*c) % p == 1]
PSL = sorted({canon(m) for m in SL}); assert len(PSL) == p*(p*p-1)//2
mm = lambda x, y: canon(((x[0]*y[0]+x[1]*y[2]) % p, (x[0]*y[1]+x[1]*y[3]) % p, (x[2]*y[0]+x[3]*y[2]) % p, (x[2]*y[1]+x[3]*y[3]) % p))
G3 = [(m, z) for m in PSL for z in range(14)]
mul3 = lambda x, y: (mm(x[0], y[0]), (x[1] + y[1]) % 14)
inv3 = lambda x: (canon((x[0][3], -x[0][1] % p, -x[0][2] % p, x[0][0])), (-x[1]) % 14)
S3 = [((1,0,0,1),0), ((2,13,14,6),6), ((4,13,7,4),12), ((2,7,7,6),10), ((6,2,8,6),1), ((6,13,15,1),9), ((1,4,12,11),11)]
S3 = [(canon(m), z) for m, z in S3]
for m, z in S3: assert (m[0]*m[3] - m[1]*m[2]) % p == 1
print("(7,8):", 2*len(G3), "vertices, diameter", haar_diam(G3, mul3, inv3, S3, (canon((1,0,0,1)), 0)))
# the automorphism alpha(x,z) = (g x g^-1, 9z) permutes S as stated
g = canon((1,3,6,0)); gi = canon((0, -3 % p, -6 % p, 1))
alpha = lambda s: (mm(mm(g, s[0]), gi), 9 * s[1] % 14)
print("alpha(S) = S:", sorted(alpha(s) for s in S3) == sorted(S3), [S3.index(alpha(s)) for s in S3])
