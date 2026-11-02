#!/usr/bin/env python3
"""lowmem_check.py SOL: low-memory diameter check of H(G,S), G = (Z_m x|_r Z_k) x Z_n, from a haar_gen3/hmeta solution
file ("d D meta m k r n NC N .." then d lines "<idx> meta(a=A,j=J) z=Z"). Same model as metacheck.py (vertices (g,A),(g,B),
edges (g,A)~(s g,B), BFS from (e,A) and (e,B) with right-multiplication symmetry), but each BFS level is computed by
sweeping all group indices in chunks of 2^20, so memory stays at a few hundred MB (metacheck.py used 1.4 GB at N = 20.9M).
Prints VALID / INVALID with the reached counts per level."""
import sys, re, time
import numpy as np

t0 = time.time()
L = open(sys.argv[1]).read().split('\n')
h = L[0].split()
d, D = int(h[0]), int(h[1])
assert h[2] == 'meta'
m, k, r = int(h[3]), int(h[4]), int(h[5])
n = int(h[h.index('n') + 1])
assert pow(r, k, m) == 1 % m, "r^k != 1 mod m"
N = m * k * n
R = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
S = []
for line in L[1:1 + d]:
    a, j = map(int, re.search(r'meta\(a=(\d+),j=(\d+)\)', line).groups())
    zm = re.search(r'z=(\d+)', line)
    z = int(zm.group(1)) if zm else 0
    S.append((a % m, j % k, z % n))
assert len(set(S)) == d and S[0] == (0, 0, 0), "generators must be distinct, first = e"


def mul(x, y):
    return ((x[0] + int(R[x[1]]) * y[0]) % m, (x[1] + y[1]) % k, (x[2] + y[2]) % n)


def inv(x):
    jj = (-x[1]) % k
    return ((-int(R[jj]) * x[0]) % m, jj, (-x[2]) % n)


rng = np.random.default_rng(5)
for _ in range(5000):
    x, y, z = [(int(rng.integers(m)), int(rng.integers(k)), int(rng.integers(n))) for _ in range(3)]
    assert mul(mul(x, y), z) == mul(x, mul(y, z)), "associativity"
    assert mul(x, inv(x)) == (0, 0, 0), "inverse"
Si = [inv(s) for s in S]


def left(s, g):
    """index array of s * g, with index(a,j,z) = (a k + j) n + z"""
    z = g % n
    t = g // n
    j = t % k
    a = t // k
    return (((s[0] + R[s[1]] * a) % m) * k + (s[1] + j) % k) * n + (s[2] + z) % n


CH = 1 << 20


def step(fr, gens):
    out = np.zeros(N, dtype=bool)
    for c0 in range(0, N, CH):
        c1 = min(N, c0 + CH)
        msk = fr[c0:c1]
        if not msk.any():
            continue
        gm = np.arange(c0, c1, dtype=np.int64)[msk]
        for s in gens:
            out[left(s, gm)] = True
    return out


def bfs(side):
    vis = [np.zeros(N, dtype=bool), np.zeros(N, dtype=bool)]
    vis[side][0] = True
    fr = vis[side].copy()
    cur = side
    levels = [1]
    for lev in range(D):
        gens = S if cur == 0 else Si   # A -> B: g -> s g ; B -> A: g -> s^-1 g
        nxt = step(fr, gens)
        nxt &= ~vis[1 - cur]
        vis[1 - cur] |= nxt
        fr = nxt
        cur = 1 - cur
        levels.append(int(nxt.sum()))
        if not nxt.any():
            break
    return int(vis[0].sum()), int(vis[1].sum()), levels


ok = True
for side, name in ((0, 'A'), (1, 'B')):
    ra, rb, lv = bfs(side)
    print(f"from (e,{name}): reached A {ra}/{N}, B {rb}/{N} within {D}; level sizes {lv}", flush=True)
    ok &= (ra == N and rb == N)
print(("VALID" if ok else "INVALID") + f" d={d} D={D} group=meta {m} {k} {r} x Z_{n} N={N} vertices={2*N} "
      f"({time.time() - t0:.0f}s)", flush=True)
sys.exit(0 if ok else 1)
