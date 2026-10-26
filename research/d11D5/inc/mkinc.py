"""W(8) + one new point x* and one new line l* with x* on l* (an 8-flag switch): flags (p_i, L_i), i = 1..8, become
(x*, L_i) and (p_i, l*), and (x*, l*) is a new flag.  sigma = delta on old points, sigma(x*) = l* (SX=line id to override).
Writes the plusopt format ("n dg", n lines of points, n sigma values).
usage: python3 mkinc.py mode seed out.in   (mode: spread | random | absolute)"""
import sys, random, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
os.chdir(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
from dcover import load
mode, seed, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
rng = random.Random(seed)
n, L, d_pt, d_ln, inv = load(8)
L = [list(s) for s in L]
col = [set() for _ in range(n)]
for s in L:
    for a in s: col[a].update(s)
def concurrent(a, b): return bool(set(L[a]) & set(L[b]))
K = int(os.environ.get("K", "9" if os.environ.get("NOINC") else "8"))
for attempt in range(100000):
    if mode == "absolute":
        ab = [p for p in range(n) if p in L[d_pt[p]]]
        pts = rng.sample(ab, K); lines = [d_pt[p] for p in pts]
        break
    if mode == "spread":
        lines = []; cand = list(range(n)); rng.shuffle(cand)
        for li in cand:
            if all(not concurrent(li, m) for m in lines): lines.append(li)
            if len(lines) == K: break
    else:
        lines = rng.sample(range(n), K)
    pts = []; ok = True
    for li in lines:
        c = [p for p in L[li] if all(p not in col[q] for q in pts)]
        if not c: ok = False; break
        pts.append(rng.choice(c))
    if ok and len(lines) == K: break
X = n
Lnew = [s[:] for s in L] + [pts[:] + ([] if os.environ.get("NOINC") else [X])]
for p, li in zip(pts, lines):
    Lnew[li].remove(p); Lnew[li].append(X)
sigma = d_pt[:] + [n]
if os.environ.get("SX"):
    sx = int(os.environ["SX"]); w = sigma.index(sx); sigma[w] = n; sigma[X] = sx
with open(out, "w") as f:
    f.write(f"{n+1} 9\n")
    for s in Lnew: f.write(" ".join(map(str, s)) + "\n")
    for v in sigma: f.write(f"{v}\n")
print("lines", lines, "points", pts, "->", out)
