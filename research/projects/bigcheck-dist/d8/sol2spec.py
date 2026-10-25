"""Convert an x2s.c solution (.sol) into a bcd lift spec, so that bcd checks it independently of x2s's own BFS.

Usage: python3 sol2spec.py SOL HEX.bin SINGER.bin OUT.spec

The base graph is rebuilt exactly as x2s.c builds it: C copies of H(q) (copy c: points c*2N + p, lines c*2N + N + l),
flag voltages from the tau-orbit classes, bijections sigma_j(tau^e p_o) = tau^(e + t_jo) l_(pi_j(o)) from copy c to
copy c + s_j. Automorphisms written into the spec (bcd checks them on the base): the torus tau acting on every copy,
and the copy rotation c -> c + 1 when C > 1. (x2l/x2d solutions are not handled.)
"""
import sys

import numpy as np

sys.path.insert(0, __file__.rsplit("/", 1)[0])
import hexspec as hs  # noqa: E402

sol, hexbin, singer, out = sys.argv[1:5]
H = hs.Hex(hexbin, singer)
q, N, KA = H.q, H.N, H.KA
NO = N // KA
lines = open(sol).read().split("\n")
hdr = lines[0].split()
assert hdr[0] == "x2s", "not an x2s solution"
get = lambda key: int(hdr[hdr.index(key) + 1])
C, R, K = get("C"), get("r"), get("k")
S = [int(x) for x in hdr[hdr.index("s") + 1: hdr.index("s") + 1 + R]]
sig = [np.array(list(map(int, lines[1 + j].split()[2:]))).reshape(NO, 3) for j in range(R)]  # pi, t, voltage
flags = np.array(list(map(int, lines[1 + R].split()[1:]))).reshape(NO, q + 1)

TL = np.empty((KA, N), dtype=np.int64); TL[0] = np.arange(N)
for e in range(1, KA):
    TL[e] = H.tl[TL[e - 1]]
edges = []
for c in range(C):
    off = c * 2 * N
    for p in range(N):
        o, e = H.porb[p], H.ppos[p]
        r = H.prep[o]
        rl = list(H.plines[r])
        for L in H.plines[p]:
            s0 = rl.index(TL[(KA - e) % KA][L])
            edges.append((off + p, off + N + L, int(flags[o, s0]) % K))
        for j in range(R):
            pi, t, va = sig[j][o]
            line = TL[(e + t) % KA][H.lrep[pi]]
            edges.append((off + p, ((c + S[j]) % C) * 2 * N + N + line, int(va) % K))
NB = C * 2 * N
tau = np.concatenate([np.concatenate([c * 2 * N + H.tp, c * 2 * N + N + H.tl]) for c in range(C)])
with open(out, "w") as f:
    f.write(f"bcd-lift 1\ngroup cyclic {K}\nvertices {NB}\nedges {len(edges)}\n")
    f.write("".join(f"{u} {v} {a}\n" for u, v, a in edges))
    f.write("aut 1\n" + " ".join(map(str, tau)) + "\n" + " ".join(["0"] * NB) + "\n")
    if C > 1:
        rot = (np.arange(NB) + 2 * N) % NB
        f.write("aut 1\n" + " ".join(map(str, rot)) + "\n" + " ".join(["0"] * NB) + "\n")
    f.write("end\n")
print(f"{sol}: q={q} C={C} r={R} k={K} -> {out} ({len(edges)} base edges, lift {NB * K} vertices)")
