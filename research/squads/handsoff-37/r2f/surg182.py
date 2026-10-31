"""Symmetric orbit insertion: F21-invariant lift of C168-type (k=12, Z7, alpha=4) -> k=13 (n=182).
Remove one sigma-orbit of 3 base edges (a_i,b_i,t_i), add a fixed A base vertex a* joined to b_0,b_1,b_2 with voltages
alpha^i c0 and a fixed B base vertex b* joined to a_0,a_1,a_2 with voltages alpha^i d0. Score all 9 x 49 choices (far, all pairs).
Writes group file (sigma' = fixed {0,1,2,12} + 3-cycles on A; fixed 12 + 3-cycles on B) and the best start graphs."""
import sys
from collections import deque
m = 7; alpha = 4
src = sys.argv[1]; outdir = sys.argv[2]
toks = open(src).read().split()
n0 = int(toks[0]); pairs = [(int(toks[i]), int(toks[i+1])) for i in range(1, len(toks), 2)]
k = 12
base = set()
for x, y in pairs:
    a, b = (x, y) if x < k * m else (y, x)
    ua, ta = divmod(a, m); ub, tb = divmod(b, m)
    # lift edge (ua,ta)-(ub,tb): voltage from the A-vertex at h=0 is (tb - ta); with the Z7 gauge of the calibration run, use h of A
    base.add((ua, ub - k, (tb - ta) % m))
# lift of base edge (a,b,t): (a,h)-(k+b,h+t); so re-derive base from vertex (a,0)
base = set()
for x, y in pairs:
    a, b = (x, y) if x < k * m else (y, x)
    ua, ha = divmod(a, m); ub, hb = divmod(b, m)
    if ha == 0:
        base.add((ua, ub - k, hb % m))
assert len(base) == 36, len(base)
# sanity: base invariance under (sigma, alpha) in the calibration labelling
pA = list(range(12)); pA[3], pA[4], pA[5] = 4, 5, 3; pA[6], pA[7], pA[8] = 7, 8, 6; pA[9], pA[10], pA[11] = 10, 11, 9
pB = list(range(12)); pB[0], pB[1], pB[2] = 1, 2, 0; pB[3], pB[4], pB[5] = 4, 5, 3; pB[6], pB[7], pB[8] = 7, 8, 6; pB[9], pB[10], pB[11] = 10, 11, 9
for (a, b, t) in base:
    assert (pA[a], pB[b], (alpha * t) % m) in base, "calibration base not invariant"
print("calibration base invariant, 36 base edges")
def orbit(e):
    a, b, t = e; out = []
    for i in range(3):
        out.append((a, b, t))
        a, b, t = pA[a], pB[b], (alpha * t) % m
    return out
orbits = []
seen = set()
for e in sorted(base):
    if e[0] < 3 or e in seen: continue   # skip fixed A vertices
    o = orbit(e)
    if len(set(x for x, _, _ in o)) != 3: continue
    seen.update(o); orbits.append(o)
print("removable orbits", len(orbits))
def lift_edges(B, kk):
    E = []
    for a, b, t in B:
        for h in range(m):
            E.append((a * m + h, (13 + b) * m + (h + t) % m))
    return E
def far_all(n, E):
    adj = [[] for _ in range(n)]
    for x, y in E: adj[x].append(y); adj[y].append(x)
    far = 0
    for s in range(n):
        d = [-1] * n; d[s] = 0; q = deque([s])
        while q:
            x = q.popleft()
            for y in adj[x]:
                if d[y] < 0: d[y] = d[x] + 1; q.append(y)
        far += sum(1 for i in range(n) if i != s and (d[i] < 0 or d[i] > 7))
    return far // 2
res = []
for oi, o in enumerate(orbits):
    rem = set(o)
    keep = [e for e in base if e not in rem]
    a0, b0, t0 = o[0]
    # order the orbit as a0 -> a1 -> a2 (sigma order) and b0 -> b1 -> b2
    A_cyc = [o[i][0] for i in range(3)]; B_cyc = [o[i][1] for i in range(3)]
    for c0 in range(m):
        for d0 in range(m):
            B2 = list(keep)
            for i in range(3):
                B2.append((12, B_cyc[i], (pow(alpha, i, m) * c0) % m))   # a* fixed, joined to B cycle
                B2.append((A_cyc[i], 12, (pow(alpha, i, m) * d0) % m))   # b* fixed, joined to A cycle
            # degree check
            from collections import Counter
            dA = Counter(a for a, _, _ in B2); dB = Counter(b for _, b, _ in B2)
            assert all(v == 3 for v in dA.values()) and len(dA) == 13, dA
            assert all(v == 3 for v in dB.values()) and len(dB) == 13, dB
            E = lift_edges(B2, 13)
            f = far_all(13 * 2 * m, E)
            res.append((f, oi, c0, d0, B2))
res.sort(key=lambda r: r[0])
print("best far (all pairs) for insertions:", [r[0] for r in res[:10]])
import os
os.makedirs(outdir, exist_ok=True)
# group file with sigma': A fixed {0,1,2,12}, cycles (3,4,5),(6,7,8),(9,10,11); B fixed 12, cycles (0,1,2),(3,4,5),(6,7,8),(9,10,11)
kk = 13; n = 2 * kk * m
sA = list(range(kk)); sA[3], sA[4], sA[5] = 4, 5, 3; sA[6], sA[7], sA[8] = 7, 8, 6; sA[9], sA[10], sA[11] = 10, 11, 9
sB = list(range(kk)); sB[0], sB[1], sB[2] = 1, 2, 0; sB[3], sB[4], sB[5] = 4, 5, 3; sB[6], sB[7], sB[8] = 7, 8, 6; sB[9], sB[10], sB[11] = 10, 11, 9
sig = sA + [kk + x for x in sB]
def vid(u, h): return u * m + (h % m)
gens = [[vid(u // m, u % m + 1) for u in range(n)], [vid(sig[u // m], alpha * (u % m)) for u in range(n)]]
ident = tuple(range(n)); G = {ident}; fr = [ident]
while fr:
    new = []
    for p in fr:
        for g in gens:
            q = tuple(g[p[x]] for x in range(n))
            if q not in G: G.add(q); new.append(q)
    fr = new
G = sorted(G)
with open(os.path.join(outdir, 'grp.txt'), 'w') as f:
    f.write('%d %d\n' % (n, len(G)))
    for p in G: f.write(' '.join(map(str, p)) + '\n')
    f.write(' '.join('0' if v // m < kk else '1' for v in range(n)) + '\n')
print('group order', len(G))
for rank, (f, oi, c0, d0, B2) in enumerate(res[:int(sys.argv[3]) if len(sys.argv) > 3 else 3]):
    E = lift_edges(B2, kk)
    with open(os.path.join(outdir, 'start_%d.txt' % rank), 'w') as fh:
        fh.write('%d\n' % n)
        for x, y in E: fh.write('%d %d\n' % (x, y))
    print('start', rank, 'far', f, 'orbit', oi, 'c0', c0, 'd0', d0)
