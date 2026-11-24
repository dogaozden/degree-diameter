#!/usr/bin/env python3
"""Low-memory independent BFS for G = F_p^2 x| Q (cay_mg group file).
usage: indep_g2.py FILE d K lev vr vc ... [lev vr vc (involution)]
Group law (u,v)(x,y) = (u x, rho(x)^-1 v + y) evaluated from matrices in pure python; elements are integers
x*p*p+y1*p+y2 (x = index of rho(x) in the file). Visited = bytearray. Prints order, layers, defect."""
import sys, struct
f = open(sys.argv[1], 'rb'); p, L = struct.unpack('ii', f.read(8))
Q = [struct.unpack('iiii', f.read(16)) for _ in range(L)]
d, K = int(sys.argv[2]), int(sys.argv[3]); rest = list(map(int, sys.argv[4:])); H = d // 2; INV = d & 1
pos = {m: i for i, m in enumerate(Q)}
def mm(X, Y): return ((X[0]*Y[0]+X[1]*Y[2]) % p, (X[0]*Y[1]+X[1]*Y[3]) % p, (X[2]*Y[0]+X[3]*Y[2]) % p, (X[2]*Y[1]+X[3]*Y[3]) % p)
def inv(X):
    det = (X[0]*X[3]-X[1]*X[2]) % p; di = pow(det, -1, p)
    return ((X[3]*di) % p, (-X[1]*di) % p, (-X[2]*di) % p, (X[0]*di) % p)
Minv = [inv(m) for m in Q]
gens = []
for i in range(H + INV):
    lev, vr, vc = rest[3*i:3*i+3]; gens.append((lev, vr, vc))
S = []   # (level index u, vector)
for i, (lev, vr, vc) in enumerate(gens):
    S.append((lev, vr, vc))
    if i < H:
        ui = pos[inv(Q[lev])]; M = Minv[ui]           # M_{u^-1} = rho(u^-1)^-1
        w0 = (M[0]*vr + M[1]*vc) % p; w1 = (M[2]*vr + M[3]*vc) % p
        S.append((ui, (-w0) % p, (-w1) % p))
# self-check of group axioms on random triples and inverses
import random
def prod(s, e):
    u, vr, vc = s; x, y1, y2 = e
    M = Minv[x]; w0 = (M[0]*vr + M[1]*vc) % p; w1 = (M[2]*vr + M[3]*vc) % p
    return (pos[mm(Q[u], Q[x])], (w0 + y1) % p, (w1 + y2) % p)
rng = random.Random(1)
for _ in range(3000):
    a = (rng.randrange(L), rng.randrange(p), rng.randrange(p)); b = (rng.randrange(L), rng.randrange(p), rng.randrange(p)); c = (rng.randrange(L), rng.randrange(p), rng.randrange(p))
    assert prod(a, prod(b, c)) == prod(prod(a, b), c), "group law not associative"
ident = (0, 0, 0)
assert Q[0] == (1, 0, 0, 1)
for i in range(H):
    lev, vr, vc = gens[i]; ui = pos[inv(Q[lev])]
    s_inv = S[2*i+1]
    assert prod((lev, vr, vc), s_inv) == ident, "inverse generator wrong"
if INV:
    lev, vr, vc = gens[H]; assert prod((lev, vr, vc), (lev, vr, vc)) == ident, "involution has order != 2"
for _ in range(500):
    g0 = (rng.randrange(L), rng.randrange(p), rng.randrange(p))
    for i in range(H):
        assert prod(S[2*i+1], prod(S[2*i], g0)) == g0, "connection set not symmetric"
N = L * p * p
vis = bytearray((N + 7) // 8)
def mark(e):
    if vis[e >> 3] >> (e & 7) & 1: return False
    vis[e >> 3] |= 1 << (e & 7); return True
mark(0)
layer = [(0, 0, 0)]; sizes = [1]; total = 1
for t in range(K):
    nxt = []
    for g in layer:
        for s in S:
            h = prod(s, g); e = (h[0]*p + h[1])*p + h[2]
            if mark(e): nxt.append(h)
    layer = nxt; sizes.append(len(nxt)); total += len(nxt)
    if not nxt: break
print("order", N, "reached", total, "defect", N - total, "layers", sizes)
