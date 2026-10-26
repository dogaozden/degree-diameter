"""Incident switch built on a regulus through an absolute point (design of research/d11D5/NOTES.md round 3).
h = hyperbolic PG(3,8)-line containing an absolute point R9 (R9 on delta(R9)); the lines delta(R) (R in h) form a
regulus; t = the transversal through R9; p_i = delta(R_i) cap t (i = 1..8).  Switch: x* on L_i = delta(R_i) instead of
p_i (i <= 8), l* = {p_1..p_8, x*}.  sigma = delta except sigma(R9) = l*, sigma(x*) = delta(R9).
Then sigma^-1(lines of x*) = h (covering set) and sigma(points of l*) = the pencil of delta(t) (dual covering set).
usage: python3 mkabs.py index out.in  (index picks the (h, R9) candidate)"""
import sys, os, json, random
D = os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."); sys.path.insert(0, D)
from dcover import load
from w8 import field
here = os.getcwd(); os.chdir(D)
n, L, d_pt, d_ln, inv = load(8)
W = json.load(open("w8.json")); pts = [tuple(v) for v in W["points"]]; os.chdir(here)
idx = {v: i for i, v in enumerate(pts)}
mul, finv = field(8)
def norm(v):
    for c in v:
        if c: s = finv[c]; return tuple(mul[s][x] for x in v)
def B(x, y): return mul[x[0]][y[1]] ^ mul[x[1]][y[0]] ^ mul[x[2]][y[3]] ^ mul[x[3]][y[2]]
def span(i, j):
    x, y = pts[i], pts[j]; s = {i, j}
    for a in range(8): s.add(idx[norm(tuple(x[k] ^ mul[a][y[k]] for k in range(4)))])
    return sorted(s)
Ls = [set(s) for s in L]
ab = [p for p in range(n) if p in Ls[d_pt[p]]]
k, out = int(sys.argv[1]), sys.argv[2]
rng = random.Random(k)
cands = []
for R9 in ab:
    for j in range(n):
        if j != R9 and B(pts[R9], pts[j]) != 0:
            h = span(R9, j)
            if len(cands) < k + 1 and tuple(h) not in [tuple(c[0]) for c in cands]: cands.append((h, R9))
    if len(cands) > k: break
h, R9 = cands[k]
Rs = [r for r in h if r != R9]
reg = [d_pt[r] for r in h]
assert all(not (Ls[reg[a]] & Ls[reg[b]]) for a in range(9) for b in range(a + 1, 9)), "regulus lines meet"
# transversal through R9: a line through R9 meeting every regulus line
ts = [l for l in range(n) if R9 in Ls[l] and l != d_pt[R9] and all(Ls[l] & Ls[m] for m in reg)]
assert ts, "no transversal"
t = ts[0]
P = [next(iter(Ls[t] & Ls[d_pt[r]])) for r in Rs]
X = n
Lnew = [sorted(s) for s in Ls] + [P + [X]]
for p, r in zip(P, Rs):
    li = d_pt[r]; Lnew[li].remove(p); Lnew[li].append(X)
sig = d_pt[:] + [None]
sig[X] = d_pt[R9]; sig[R9] = n
assert sorted(sig) == list(range(n + 1))
with open(out, "w") as f:
    f.write(f"{n+1} 9\n")
    for s in Lnew: f.write(" ".join(map(str, s)) + "\n")
    for v in sig: f.write(f"{v}\n")
print("h", h, "R9", R9, "t", t, "P", P, "->", out)
