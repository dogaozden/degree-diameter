#!/usr/bin/env python3
"""hubfix.py: degree-preserving 2-switches in the hub graph aimed at the far hub pairs reported by hubfar.c.
For a far same-side pair (u, w): pick y adjacent to w and edges (u, p), (x, y) with x != u, w; replace them by (u, y),
(x, p) when both are new (then d(u, w) <= 2 in the hub graph).  Pairs involving a non-hub vertex are reported (they
would contradict the theorem).  usage: hubfix.py HUBEDGES FAR.txt NV0 KB SEED OUT.txt"""
import sys, numpy as np
hef, farf, NV0, KB, seed, out = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
rng = np.random.default_rng(seed)
he = [tuple(r) for r in np.loadtxt(hef, dtype=np.int64).tolist()]
E = set(he)
nbL, nbP = {}, {}
for a, b in E: nbL.setdefault(a, set()).add(b); nbP.setdefault(b, set()).add(a)
pairs = set()
for line in open(farf):
    t = line.split()
    if t[0] != 'far': continue
    s, x = int(t[1]), int(t[2])
    if x < NV0 or s < NV0: print('NON-HUB far pair', s, x); continue
    s -= NV0; x -= NV0
    sb, xb = s < KB, x < KB
    if sb != xb: print('opposite-side far pair', s, x); continue
    pairs.add((min(s, x), max(s, x)))
print(len(pairs), 'unordered far hub pairs')
done = 0
for u, w in sorted(pairs):
    side = 0 if u < KB else 1
    if side == 1: u -= KB; w -= KB
    for _ in range(200):
        if side == 0:
            y = rng.choice(sorted(nbL[w])); p = rng.choice(sorted(nbL[u])); xs = sorted(nbP[y] - {u, w})
            if not xs or y in nbL[u]: continue
            x = rng.choice(xs)
            if p in nbL[x]: continue
            E -= {(u, p), (x, y)}; E |= {(u, y), (x, p)}
            nbL[u].discard(p); nbL[u].add(y); nbL[x].discard(y); nbL[x].add(p)
            nbP[p].discard(u); nbP[p].add(x); nbP[y].discard(x); nbP[y].add(u)
        else:
            y = rng.choice(sorted(nbP[w])); p = rng.choice(sorted(nbP[u])); xs = sorted(nbL[y] - {u, w})
            if not xs or y in nbP[u]: continue
            x = rng.choice(xs)
            if p in nbP[x]: continue
            E -= {(p, u), (y, x)}; E |= {(y, u), (p, x)}
            nbP[u].discard(p); nbP[u].add(y); nbP[x].discard(y); nbP[x].add(p)
            nbL[p].discard(u); nbL[p].add(x); nbL[y].discard(x); nbL[y].add(u)
        done += 1; break
print(done, 'switches')
np.savetxt(out, np.array(sorted(E), dtype=np.int64), fmt='%d')
