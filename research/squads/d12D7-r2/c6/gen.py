"""gen.py SEED OUT.hubs3 [NEWCOUNT]: extend the 693,100 layout by NEWCOUNT (default 200) hubs per side.
New hubs take the free owner slots (per level, each freed index o has 2 - used slots), owners chosen at random.
Hub graph: old edges kept; new L-hubs (indices 14400..) and new P-hubs (14400..) joined by NEWCOUNT-regular bipartite
random matchings (degree 7 each), no multi-edges. Old hubs are untouched."""
import sys, random
SEED, OUT = int(sys.argv[1]), sys.argv[2]
K_NEW = int(sys.argv[3]) if len(sys.argv) > 3 else 200
D = 7
rng = random.Random(SEED)
SRC = "/home/user/degree-diameter/research/frontier/sols/d12D7_hex9_spread730_clhaarPSL9x40_n693100.hubs3"
with open(SRC) as f:
    HL, HP, m = map(int, f.readline().split())
    Lown = [list(map(int, f.readline().split())) for _ in range(HL)]
    Pown = [list(map(int, f.readline().split())) for _ in range(HP)]
    E = [tuple(map(int, f.readline().split())) for _ in range(m)]
K = 7300
useL = [[0]*5 for _ in range(K)]; useP = [[0]*5 for _ in range(K)]
for row in Lown:
    for i, o in enumerate(row): useL[o][i] += 1
for row in Pown:
    for i, o in enumerate(row): useP[o][i] += 1
assert all(useL[o][i] <= 2 and useP[o][i] <= 2 for o in range(K) for i in range(5))
def free_list(use):
    out = []
    for i in range(5):
        F = [o for o in range(K) for _ in range(2 - use[o][i])]
        rng.shuffle(F); out.append(F)
    return out
FL, FP = free_list(useL), free_list(useP)
print("free slots per level L:", [len(F) for F in FL], "P:", [len(F) for F in FP], file=sys.stderr)
assert all(len(F) >= K_NEW for F in FL) and all(len(F) >= K_NEW for F in FP)
newL = [[FL[i][t] for i in range(5)] for t in range(K_NEW)]
newP = [[FP[i][t] for i in range(5)] for t in range(K_NEW)]
# hub graph among new hubs: circulant 7-regular start, randomized by double-edge swaps (simple, bipartite)
offs = rng.sample(range(K_NEW), D)
E2 = [(j, (j + s) % K_NEW) for j in range(K_NEW) for s in offs]
Eset = set(E2); El = list(Eset)
for _ in range(60000):
    a = rng.randrange(len(El)); b = rng.randrange(len(El))
    (j1, k1), (j2, k2) = El[a], El[b]
    if j1 == j2 or k1 == k2: continue
    n1, n2 = (j1, k2), (j2, k1)
    if n1 in Eset or n2 in Eset: continue
    Eset.discard((j1, k1)); Eset.discard((j2, k2)); Eset.add(n1); Eset.add(n2)
    El[a], El[b] = n1, n2
edges = Eset
assert len(edges) == D * K_NEW
deg_l = [0]*K_NEW; deg_p = [0]*K_NEW
for j, k in edges: deg_l[j] += 1; deg_p[k] += 1
assert all(x == D for x in deg_l) and all(x == D for x in deg_p)
NL, NP = HL + K_NEW, HP + K_NEW
with open(OUT, "w") as f:
    f.write(f"{NL} {NP} {m + len(edges)}\n")
    for row in Lown + newL: f.write(" ".join(map(str, row)) + "\n")
    for row in Pown + newP: f.write(" ".join(map(str, row)) + "\n")
    for j, k in E: f.write(f"{j} {k}\n")
    for j, k in sorted(edges): f.write(f"{HL + j} {HP + k}\n")
print(f"wrote {OUT}: HL={NL} HP={NP} m={m + len(edges)}", file=sys.stderr)
