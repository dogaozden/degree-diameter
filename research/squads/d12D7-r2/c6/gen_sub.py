"""gen_sub.py SEED OUT.hubs3 NNEW: add NNEW L-hubs and NNEW P-hubs; each new L-hub a (and each new P-hub b) takes 7
old-edge subdivisions: an old edge (j,k) is removed and replaced by (j, b) and (a, k), so every old hub keeps degree 7
and every new hub gets degree 7. The NNEW new L-hubs use the free owner slots; old-edge choices are random and disjoint."""
import sys, random
SEED, OUT, NNEW = int(sys.argv[1]), sys.argv[2], int(sys.argv[3])
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
def free_list(use):
    out = []
    for i in range(5):
        F = [o for o in range(K) for _ in range(2 - use[o][i])]
        rng.shuffle(F); out.append(F)
    return out
FL, FP = free_list(useL), free_list(useP)
newL = [[FL[i][t] for i in range(5)] for t in range(NNEW)]
newP = [[FP[i][t] for i in range(5)] for t in range(NNEW)]
# choose 7*NNEW old edges, disjoint in both endpoints
idx = list(range(m)); rng.shuffle(idx)
used_j, used_k, chosen = set(), set(), []
for e in idx:
    j, k = E[e]
    if j in used_j or k in used_k: continue
    used_j.add(j); used_k.add(k); chosen.append(e)
    if len(chosen) == 7 * NNEW: break
assert len(chosen) == 7 * NNEW, len(chosen)
rem = set(chosen)
newE = []
for t in range(NNEW):
    a = HL + t; b = HP + t          # L-index and P-index of the new hubs
    for s in range(7):
        e = chosen[7 * t + s]; j, k = E[e]
        newE.append((j, HP + t))    # old L-hub j to new P-hub t
        newE.append((HL + t, k))    # new L-hub t to old P-hub k
NL, NP = HL + NNEW, HP + NNEW
keep = [E[e] for e in range(m) if e not in rem]
with open(OUT, "w") as f:
    f.write(f"{NL} {NP} {len(keep) + len(newE)}\n")
    for row in Lown + newL: f.write(" ".join(map(str, row)) + "\n")
    for row in Pown + newP: f.write(" ".join(map(str, row)) + "\n")
    for j, k in keep: f.write(f"{j} {k}\n")
    for j, k in newE: f.write(f"{j} {k}\n")
print(f"wrote {OUT}: HL={NL} HP={NP} m={len(keep)+len(newE)}", file=sys.stderr)
