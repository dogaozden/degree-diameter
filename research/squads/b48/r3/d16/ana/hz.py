import sys, random
import numpy as np
# meta m k r: index a + m*j, (a,j)(b,l) = (a + r^j b, j + l); Haar graph (0,x) ~ (1, x*s), lift convention
m, k, r = 104, 24, 7
if len(sys.argv) > 3: m, k, r = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
N = m * k
rp = np.array([pow(r, j, m) for j in range(k)])
A_ = np.arange(N); a_, j_ = A_ % m, A_ // m
mul = (((a_[:, None] + rp[j_][:, None] * a_[None, :]) % m) + m * ((j_[:, None] + j_[None, :]) % k)).astype(np.int32)
inv = np.argmax(mul == 0, axis=1)
def dist_from(src, S, Si):
    """BFS on the 2N-vertex Haar graph; ids: A = x, B = N + y. returns dist array (-1 = unreached)."""
    d = np.full(2 * N, -1, dtype=np.int32); d[src] = 0
    fr = np.array([src]); lvl = 0
    while fr.size:
        lvl += 1
        fa = fr[fr < N]; fb = fr[fr >= N] - N
        nxt = []
        if fa.size: nxt.append(N + mul[fa][:, S].ravel())
        if fb.size: nxt.append(mul[fb][:, Si].ravel())
        if not nxt: break
        nb = np.unique(np.concatenate(nxt))
        nb = nb[d[nb] < 0]; d[nb] = lvl; fr = nb
    return d
def far_list(S, D=9):
    S = np.array(S); Si = inv[S]
    out = {}
    for src, name in ((0, "A"), (N, "B")):
        d = dist_from(src, S, Si)
        out[name] = np.where((d > D) | (d < 0))[0].tolist()
    return out
def cost(S, D=9):
    f = far_list(S, D); return len(f["A"]) + len(f["B"]), f
def lab(x):
    x = x % N
    return "(%d,%d)" % (x % m, x // m)
if __name__ == "__main__":
    S0 = [0, 1392, 1750, 1537]
    c, f = cost(S0)
    print("check lift S", c, [(s, lab(s)) for s in f["A"]], [(s, lab(s)) for s in f["B"]])
