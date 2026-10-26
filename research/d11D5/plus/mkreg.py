"""Regulus switch: h hyperbolic PG-line, L_j = delta(R_j) (R_j in h, a regulus), p_j = L_j cap t (transversal t),
sigma = delta with swaps sigma(p_j)<->sigma(y_j), y_j = L_j cap t' (transversal t'), and sigma(delta(L_j))<->sigma(delta(m_j)).
usage: python3 mkreg.py hindex ti tpi seed out.in"""
import json, sys, random, os
sys.path.insert(0, "/home/user/degree-diameter/research/d11D5"); here = os.getcwd(); os.chdir("/home/user/degree-diameter/research/d11D5")
from dcover import load
n, L, d_pt, d_ln, inv = load(8)
W = json.load(open("w8.json")); P = [tuple(v) for v in W["points"]]
cand = json.load(open("plus/hcand.json")); os.chdir(here)
hi, ti, tpi, seed, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
rng = random.Random(seed)
c = cand[hi]; lines = c["L"]; tp = set(c["trans"][tpi])
if ti >= 0:
    t = set(c["trans"][ti]); pts = [next(iter(set(L[l]) & t)) for l in lines]
else:   # permutation: p_j on transversal pi(j), all different from tpi
    others = [k for k in range(9) if k != tpi]
    perm = others[:]; rng.shuffle(perm)
    pts = [next(iter(set(L[l]) & set(c["trans"][perm[j % 8]]))) for j, l in enumerate(lines)]
    # 9 lines but only 8 transversals avoid tpi: the 9th reuses one (one collinear pair)
ys = [next(iter(set(L[l]) & tp)) for l in lines]
col = [set() for _ in range(n)]
for s in L:
    for a in s: col[a].update(s)
ncol = sum(1 for i in range(9) for j in range(i + 1, 9) if pts[j] in col[pts[i]])
Lb = [list(s) for s in L]
X = n
for p, l in zip(pts, lines): Lb[l].remove(p); Lb[l].append(X)
Lb.append(pts[:])
sig = d_pt[:] + [n]; pos = {l: i for i, l in enumerate(sig)}
def swap(a, b):
    sig[a], sig[b] = sig[b], sig[a]; pos[sig[a]] = a; pos[sig[b]] = b
for p, y, l in zip(pts, ys, lines):
    if y != p: swap(p, y)
    ms = [m for m in range(n) if p in L[m] and m != l]
    swap(pos[l], pos[rng.choice(ms)])
with open(out, "w") as g:
    g.write(f"{n+1} 9\n")
    for s in Lb: g.write(" ".join(map(str, s)) + "\n")
    g.write("\n".join(map(str, sig)) + "\n")
json.dump({"lines": lines, "pts": pts, "ys": ys}, open(out + ".json", "w"))
print("collinear p-pairs", ncol, "y==p", sum(1 for a, b in zip(pts, ys) if a == b))
