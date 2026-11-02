#!/usr/bin/env python3
"""metacheck.py SOL: independent diameter check of a Haar graph H(G,S), G = (Z_m x|_r Z_k) x Z_n, from a haar_gen3
solution file ("d D meta m k r n NC N .." then d lines "<idx> meta(a=A,j=J) z=Z"). Own group code (no haar_gen3 code):
(a,j,z)(b,l,w) = (a + r^j b mod m, j + l mod k, z + w mod n); r^k = 1 mod m is checked, and associativity on random
triples. Vertices (g,A), (g,B); edges (g,A) ~ (s g, B). Right multiplication by G is an automorphism transitive on each
side, so BFS from (e,A) and from (e,B), each reaching all 2N vertices within D, is exactly diameter <= D.
Prints VALID / INVALID with level sizes."""
import sys, re, time, numpy as np
t0 = time.time()
L = open(sys.argv[1]).read().split('\n'); h = L[0].split()
d, D = int(h[0]), int(h[1]); assert h[2] == 'meta'
m, k, r = int(h[3]), int(h[4]), int(h[5]); i = h.index('n'); n = int(h[i + 1])
assert pow(r, k, m) == 1 % m, "r^k != 1 mod m"
N = m * k * n; R = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
S = []
for line in L[1:1 + d]:
    a, j = map(int, re.search(r'meta\(a=(\d+),j=(\d+)\)', line).groups())
    zm = re.search(r'z=(\d+)', line); z = int(zm.group(1)) if zm else 0
    S.append((a % m, j % k, z % n))
assert len(set(S)) == d and S[0] == (0, 0, 0), "generators must be distinct, first = e"
def mul(x, y): return ((x[0] + int(R[x[1]]) * y[0]) % m, (x[1] + y[1]) % k, (x[2] + y[2]) % n)
def inv(x): jj = (-x[1]) % k; return ((-int(R[jj]) * x[0]) % m, jj, (-x[2]) % n)
rng = np.random.default_rng(3)
for _ in range(20000):
    x, y, z = [(int(rng.integers(m)), int(rng.integers(k)), int(rng.integers(n))) for _ in range(3)]
    assert mul(mul(x, y), z) == mul(x, mul(y, z)) and mul(x, inv(x)) == (0, 0, 0)
Si = [inv(s) for s in S]
def idx(a, j, z): return (a * k + j) * n + z
def left(s, g):   # s * g for an index array g
    z = g % n; t = g // n; j = t % k; a = t // k
    return idx((s[0] + R[s[1]] * a) % m, (s[1] + j) % k, (s[2] + z) % n)
def bfs(side):
    vis = [np.zeros(N, bool), np.zeros(N, bool)]; vis[side][0] = True
    fr = np.array([0], dtype=np.int64); cur = side; levels = [1]
    for lev in range(D):
        gens = S if cur == 0 else Si           # A -> B: g -> s g ; B -> A: g -> s^-1 g
        nxt = np.unique(np.concatenate([left(s, fr) for s in gens]))
        nxt = nxt[~vis[1 - cur][nxt]]; vis[1 - cur][nxt] = True
        fr = nxt; cur = 1 - cur; levels.append(len(nxt))
        if len(fr) == 0: break
    return int(vis[0].sum()), int(vis[1].sum()), levels
ok = True
for side, name in ((0, 'A'), (1, 'B')):
    ra, rb, lv = bfs(side)
    print(f"from (e,{name}): reached A {ra}/{N}, B {rb}/{N} within {D}; level sizes {lv}")
    ok &= (ra == N and rb == N)
print(("VALID" if ok else "INVALID") + f" d={d} D={D} group=meta {m} {k} {r} x Z_{n} N={N} vertices={2*N} ({time.time()-t0:.0f}s)")
sys.exit(0 if ok else 1)
