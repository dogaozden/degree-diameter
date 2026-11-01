#!/usr/bin/env python3
"""holes_dist.py SOL: true graph distance from (e,A) and (e,B) to every vertex (no radius cut), and the
distance profile of the holes at radius D. Also which generator-words of minimal length reach each hole."""
import sys
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/raise10/r2/e14')
from anatlib import parse, Gp
d, D, m, k, r, S = parse(sys.argv[1])
Gr = Gp(m, k, r); N = Gr.N
Si = [Gr.inv(s) for s in S]
def full(side):
    dist = [np.full(N, -1), np.full(N, -1)]; dist[side][0] = 0
    fr = np.array([0], dtype=np.int64); cur = side; lev = 0
    while len(fr):
        lev += 1
        gens = S if cur == 0 else Si
        nxt = np.unique(np.concatenate([Gr.left(s, fr) for s in gens]))
        nxt = nxt[dist[1 - cur][nxt] < 0]; dist[1 - cur][nxt] = lev
        fr = nxt; cur = 1 - cur
    return dist
for side, nm in ((0, 'A'), (1, 'B')):
    dist = full(side)
    tgt = dist[1 - side]
    print(f"source (e,{nm}): ecc on target side = {tgt.max()}, unreached in graph {np.sum(tgt<0)}")
    print("  distance histogram on target side:", np.bincount(tgt[tgt>=0]).tolist())
    holes = np.nonzero(tgt > D)[0]
    hd = [(int(h)//k, int(h)%k, int(tgt[h])) for h in holes]
    print(f"  holes (a,j,dist): {hd}")
