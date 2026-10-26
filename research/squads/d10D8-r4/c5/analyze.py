"""c5: per-pair residual analysis of a lift (Python bitmask BFS, same semantics as lift3 ITERS=0)."""
import sys, collections
sys.path.insert(0, "/home/user/degree-diameter/research/squads/d10D8-r4/c5")
from rule import *

def read_sol(path):
    toks = open(path).read().split("\n")
    q, J, m, D = map(int, toks[0].split()[:4]); N = None
    H = None
    return q, J, m, D, toks

def residual(q, m, sigs, mvs, hv, D=8):
    H = load_hex(q); N = H["N"]; Q1 = H["Q1"]; pl = H["pl"]
    V = 2 * N; FULL = (1 << m) - 1
    # base adjacency: nb[v] = list of (u, g) meaning arc u -> v carries voltage g (walk from u to v adds g)
    adj = [[] for _ in range(V)]
    for l in range(N):
        for k in range(Q1):
            p = pl[l * Q1 + k]; g = hv[l * Q1 + k]
            adj[N + l].append((p, (-g) % m))      # arc line -> point carries -g (walk from line to point)
            adj[p].append((N + l, g))             # arc point -> line carries g
    for t in range(len(sigs)):
        for p in range(N):
            l = sigs[t][p]; g = mvs[t][p]
            adj[N + l].append((p, (-g) % m)); adj[p].append((N + l, g))
    def rot(M, g):
        g %= m
        return ((M << g) | (M >> (m - g))) & FULL if g else M
    unc = {}   # (x, y) -> uncovered levels bitmask
    total = 0
    for x in range(V):
        W = [0] * V; W[x] = 1
        Acc = W[:]
        for k in range(1, D + 1):
            Wn = [0] * V
            for y in range(V):
                o = 0
                for (u, g) in adj[y]:          # adj[y] holds (u, voltage of arc y->u); walk u->y shifts by -g
                    if W[u]: o |= rot(W[u], -g)
                Wn[y] = o
            W = Wn
            if k >= D - 1:
                Acc = [a | b for a, b in zip(Acc, W)]
        for y in range(V):
            miss = FULL & ~Acc[y]
            if miss:
                unc[(x, y)] = miss; total += bin(miss).count("1")
    return total, unc, H

if __name__ == "__main__":
    pass
