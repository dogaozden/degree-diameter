import sys, os
sys.path.insert(0, "/home/user/degree-diameter/research/d11D5/dc")
from gq import *   # W(8) geometry: n0, LINES, d_pt, PTS, Bf, span, is_W, pmap, matinv, randmat, IDX
def read(path):
    with open(path) as f:
        toks = f.read().split()
    n, dg = int(toks[0]), int(toks[1])
    p = 2; L = []
    for _ in range(n):
        L.append([int(x) for x in toks[p:p+dg]]); p += dg
    sig = [int(x) for x in toks[p:p+n]]
    return n, L, sig
def write(path, n, L, sig):
    with open(path, "w") as f:
        f.write(f"{n} 9\n")
        for l in L: f.write(" ".join(map(str, l)) + "\n")
        for s in sig: f.write(f"{s}\n")
