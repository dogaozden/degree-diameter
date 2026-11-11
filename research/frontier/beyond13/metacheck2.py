#!/usr/bin/env python3
"""metacheck2.py SOL: independent diameter check of a Haar graph H(G,S) for G = M1 x ... x Mt x Z_n, each Mi a
metacyclic group Z_m x|_r Z_k, from a haar_gen3 solution file: header "d D meta m k r n NC .." or
"d D prod meta m k r meta m' k' r' n NC ..", generator lines "<idx> meta(a=A,j=J) z=Z" or
"<idx> prod[meta(a=A,j=J);meta(a=B,j=L)] z=Z". Own group code: (a,j)(b,l) = (a + r^j b mod m, j + l mod k) in each
factor, componentwise product. r^k = 1 mod m and associativity on random triples are checked. Vertices (g,A), (g,B);
edges (g,A) ~ (s g, B). Right multiplication by G is an automorphism transitive on each side, so BFS from (e,A) and
from (e,B), each reaching all 2N vertices within D, is exactly diameter <= D. Prints VALID / INVALID."""
import sys, re, time, numpy as np
t0 = time.time()
L = open(sys.argv[1]).read().split('\n'); h = L[0].split()
d, D = int(h[0]), int(h[1]); i = 2; F = []
if h[i] == 'prod': i += 1
while h[i] == 'meta':
    m, k, r = int(h[i + 1]), int(h[i + 2]), int(h[i + 3]); assert pow(r, k, m) == 1 % m, "r^k != 1"
    F.append((m, k, np.array([pow(r, j, m) for j in range(k)], dtype=np.int64))); i += 4
assert h[i] == 'n'; n = int(h[i + 1])
sizes = [m * k for m, k, _ in F] + [n]; N = int(np.prod(sizes, dtype=np.int64))
S = []
for line in L[1:1 + d]:
    pairs = [tuple(map(int, x)) for x in re.findall(r'meta\(a=(\d+),j=(\d+)\)', line)]
    assert len(pairs) == len(F)
    zm = re.search(r'z=(\d+)', line); z = int(zm.group(1)) if zm else 0
    S.append(tuple((a % m, j % k) for (a, j), (m, k, _) in zip(pairs, F)) + (z % n,))
assert len(set(S)) == d and all(x == (0, 0) for x in S[0][:-1]) and S[0][-1] == 0, "distinct generators, first = e"
def mul(x, y): return tuple(((x[t][0] + int(R[x[t][1]]) * y[t][0]) % m, (x[t][1] + y[t][1]) % k) for t, (m, k, R) in enumerate(F)) + ((x[-1] + y[-1]) % n,)
def inv(x):
    out = []
    for t, (m, k, R) in enumerate(F):
        jj = (-x[t][1]) % k; out.append(((-int(R[jj]) * x[t][0]) % m, jj))
    return tuple(out) + ((-x[-1]) % n,)
rng = np.random.default_rng(5)
def rnd(): return tuple((int(rng.integers(m)), int(rng.integers(k))) for m, k, _ in F) + (int(rng.integers(n)),)
e = tuple((0, 0) for _ in F) + (0,)
for _ in range(20000):
    x, y, z = rnd(), rnd(), rnd()
    assert mul(mul(x, y), z) == mul(x, mul(y, z)) and mul(x, inv(x)) == e
Si = [inv(s) for s in S]
# index: mixed radix over factors (a*k + j), then z
def decode(g):
    out = []; z = g % n; g = g // n
    for m, k, _ in reversed(F):
        t = g % (m * k); g = g // (m * k); out.append((t // k, t % k))
    return out[::-1], z
def encode(parts, z):
    g = np.zeros_like(z)
    for (a, j), (m, k, _) in zip(parts, F): g = g * (m * k) + a * k + j
    return g * n + z
def left(s, g):
    parts, z = decode(g)
    newp = [((s[t][0] + R[s[t][1]] * a) % m, (s[t][1] + j) % k) for t, ((a, j), (m, k, R)) in enumerate(zip(parts, F))]
    return encode(newp, (s[-1] + z) % n)
assert int(encode(*decode(np.array([12345 % N]))) [0]) == 12345 % N
def bfs(side):
    vis = [np.zeros(N, bool), np.zeros(N, bool)]; vis[side][0] = True
    fr = np.array([0], dtype=np.int64); cur = side; levels = [1]
    for lev in range(D):
        gens = S if cur == 0 else Si
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
spec = ' x '.join(f'meta {m} {k}' for m, k, _ in F)
print(("VALID" if ok else "INVALID") + f" d={d} D={D} group={spec} x Z_{n} N={N} vertices={2*N} ({time.time()-t0:.0f}s)")
sys.exit(0 if ok else 1)
