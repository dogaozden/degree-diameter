import re
import numpy as np
def parse(path):
    L = open(path).read().split('\n'); h = L[0].split()
    d, D = int(h[0]), int(h[1]); m, k, r = int(h[3]), int(h[4]), int(h[5])
    S = []
    for line in L[1:1 + d]:
        a, j = map(int, re.search(r'meta\(a=(\d+),j=(\d+)\)', line).groups()); S.append((a % m, j % k))
    return d, D, m, k, r, S
class Gp:
    def __init__(s, m, k, r):
        s.m, s.k, s.r = m, k, r; s.R = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64); s.N = m * k
    def mul(s, x, y): return ((x[0] + int(s.R[x[1]]) * y[0]) % s.m, (x[1] + y[1]) % s.k)
    def inv(s, x):
        jj = (-x[1]) % s.k; return ((-int(s.R[jj]) * x[0]) % s.m, jj)
    def left(s, g, fr):
        j = fr % s.k; a = fr // s.k
        return ((g[0] + s.R[g[1]] * a) % s.m) * s.k + (g[1] + j) % s.k
def reach(Gr, S, side, D):
    """dist from (e,side) on the Haar graph; returns array of distances (-1 if unreached within D) on side 'side'
    and the other side, concatenated as dist[side] (N,) -- we return distances on the TARGET side (opposite to parity)."""
    Si = [Gr.inv(s) for s in S]
    N = Gr.N
    vis = [np.full(N, -1), np.full(N, -1)]; vis[side][0] = 0
    fr = np.array([0], dtype=np.int64); cur = side
    for lev in range(1, D + 1):
        gens = S if cur == 0 else Si
        nxt = np.unique(np.concatenate([Gr.left(s, fr) for s in gens]))
        nxt = nxt[vis[1 - cur][nxt] < 0]; vis[1 - cur][nxt] = lev
        fr = nxt; cur = 1 - cur
        if len(fr) == 0: break
    return vis[1 - side]
