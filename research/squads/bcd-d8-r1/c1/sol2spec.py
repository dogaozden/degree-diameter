"""Convert an x2s/x2mc .sol (C=1, r=2 default design) into a bcd lift spec and print the bcd results.

usage: python3 sol2spec.py SOL OUT.spec [--check]
Rebuilds the base graph exactly as x2s.c does (flag classes via tau-orbit reps, matchings sigma_j with orbit data).
"""
import sys
import numpy as np
sys.path.insert(0, "/home/user/degree-diameter/research/projects/bigcheck-dist/d8")
import hexspec as hs

sol, out = sys.argv[1], sys.argv[2]
H = hs.Hex("/tmp/bcdt/hex/hex_q5.bin", "/tmp/bcdt/hex/singer_q5.bin")
q, N, KA = H.q, H.N, H.KA
toks = open(sol).read().split("\n")
hdr = toks[0].split()
K = int(hdr[hdr.index("k") + 1]); R = int(hdr[hdr.index("r") + 1]); C = int(hdr[hdr.index("C") + 1])
assert C == 1 and R == 2, hdr
NO = N // KA
sig = []
for j in range(R):
    vals = list(map(int, toks[1 + j].split()[2:]))
    arr = np.array(vals).reshape(NO, 3)
    sig.append(arr)  # columns: pi, t, va
flags = np.array(list(map(int, toks[1 + R].split()[1:]))).reshape(NO, q + 1)
S = [int(x) for x in hdr[hdr.index("s") + 1: hdr.index("s") + 1 + R]]
assert S == [0] * R, S

# tau powers on lines: TLP[e][l] = tau^e(l)
TLP = np.empty((KA, N), dtype=np.int64); TLP[0] = np.arange(N)
for e in range(1, KA):
    TLP[e] = H.tl[TLP[e - 1]]
TPP = np.empty((KA, N), dtype=np.int64); TPP[0] = np.arange(N)
for e in range(1, KA):
    TPP[e] = H.tp[TPP[e - 1]]
pl = H.plines  # pl[p][slot] = line
edges = []
edges_base = []
for p in range(N):
    o, e = H.porb[p], H.ppos[p]
    r = H.prep[o]
    for s in range(q + 1):
        L = pl[p][s]
        L0 = TLP[(KA - e) % KA][L]
        s0 = [k for k in range(q + 1) if pl[r][k] == L0]
        assert len(s0) == 1
        cls = o * (q + 1) + s0[0]
        edges.append((p, N + L, int(flags.flat[cls]) % K))
    for j in range(R):
        pi, t, va = sig[j][o]
        line = TLP[(e + t) % KA][H.lrep[pi]]
        edges.append((p, N + line, int(va) % K))
# dedupe check: each base edge once
assert len(set((u, v) for u, v, _ in edges)) == len(edges)
hs.write_spec(out, H, K, edges, tau_invariant=True)
print("wrote", out, "edges", len(edges), "M", K)
if "--check" in sys.argv:
    print("cost", hs.bcd_cost(out, 8, 8))
    print("valid", hs.bcd_check(out, 8, 8))
