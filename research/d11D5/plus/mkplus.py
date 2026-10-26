"""W(8) + one new point x* and one new line l* by a 9-flag switch, + doubled matching sigma (delta extended), for
zcons (DM mode: Z3 x Z2, jump copies fixed 4 and 1 = Z6 voltages 1 and 4) and liftcheck.
Switch: flags (p_i, L_i), i=1..9, are replaced by (x*, L_i) and (p_i, l*).  sigma = delta on old points, sigma(x*) = l*.
usage: python3 mkplus.py mode seed out_base.txt   (mode: spread | random)"""
import sys, json, random, itertools
sys.path.insert(0, "..")
from dcover import load
mode, seed, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
rng = random.Random(seed)
n, L, d_pt, d_ln, inv = load(8)
L = [list(s) for s in L]
col = [set() for _ in range(n)]
for s in L:
    for a in s: col[a].update(s)
pl = [[] for _ in range(n)]
for li, s in enumerate(L):
    for p in s: pl[p].append(li)
def concurrent(a, b): return bool(set(L[a]) & set(L[b]))
for attempt in range(100000):
    if mode == "spread":
        # greedy pairwise non-concurrent lines, then pairwise non-collinear points on them
        lines = []
        cand = list(range(n)); rng.shuffle(cand)
        for li in cand:
            if all(not concurrent(li, m) for m in lines): lines.append(li)
            if len(lines) == 9: break
    else:
        lines = rng.sample(range(n), 9)
    pts = []
    ok = True
    for li in lines:
        c = [p for p in L[li] if all(p not in col[q] for q in pts)]
        if not c: ok = False; break
        pts.append(rng.choice(c))
    if ok and len(lines) == 9: break
X, Lst = n, n  # new point index n, new line index n
NP = n + 1
Lnew = [s[:] for s in L] + [pts[:]]
for p, li in zip(pts, lines):
    Lnew[li].remove(p); Lnew[li].append(X)
sigma = d_pt[:] + [n]
edges = []; nf = 0
for li in range(NP):
    for p in Lnew[li]:
        edges.append((p, NP + li, 0, nf)); nf += 1
for J in (4, 1):
    for p in range(NP):
        edges.append((p, NP + sigma[p], J, -1))
with open(out, "w") as f:
    f.write(f"{2*NP} {nf} 0 3\n")
    for e in edges: f.write("%d %d %d %d\n" % e)
json.dump({"lines": lines, "pts": pts, "Lnew": Lnew, "sigma": sigma}, open(out + ".json", "w"))
print("switch lines", lines, "points", pts, "->", out)
