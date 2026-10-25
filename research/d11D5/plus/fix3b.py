"""Coordinated demand-preserving swaps for the fibres of x* and l* on a mkreg.py configuration.
usage: python3 fix3.py base.in meta.json outprefix"""
import sys, json, os, subprocess, itertools
sys.path.insert(0, "/home/user/degree-diameter/research/d11D5"); here = os.getcwd(); os.chdir("/home/user/degree-diameter/research/d11D5")
from dcover import load
n0, L0, d_pt, d_ln, inv = load(8); os.chdir(here)
base, meta, outp = sys.argv[1], json.load(open(sys.argv[2])), sys.argv[3]
lines, pts = meta["lines"], meta["pts"]
f = open(base); n, dg = map(int, f.readline().split())
Lb = [list(map(int, f.readline().split())) for _ in range(n)]
sig0 = [int(f.readline()) for _ in range(n)]
X = n - 1
Lset0 = [set(s) for s in L0]
R = [d_ln[l] for l in lines]                       # R_k = delta(L_k), points of h
col0 = [set() for _ in range(n0)]
for s in L0:
    for a in s: col0[a].update(s)
def line_through(a, b):
    for l in range(n0):
        if a in Lset0[l] and b in Lset0[l]: return l
    return None
def wr(fn, sig):
    with open(fn, "w") as g:
        g.write(f"{n} {dg}\n"); [g.write(" ".join(map(str, s)) + "\n") for s in Lb]; g.write("\n".join(map(str, sig)) + "\n")
def score(sig):
    wr("/tmp/f3.in", sig); o = subprocess.run(["./plusopt2", "/tmp/f3.in"], env={"SCORE": "1"}, capture_output=True, text=True).stdout
    return int(o.split("cost=")[1].split()[0])
def swapv(sig, a, b): sig[a], sig[b] = sig[b], sig[a]
print("start", score(sig0))
# x*-fix options
xfix = []
for j in range(9):
    dpj = d_pt[pts[j]]
    for k in range(9):
        if k == j: continue
        inter = Lset0[dpj] & Lset0[lines[k]]
        for z in inter:
            if z == pts[k]: continue
            # line through R_k meeting L_j
            lk = None
            for c in L0[lines[j]]:
                if c in col0[R[k]] and c != R[k]:
                    lk = line_through(R[k], c); break
            if lk is None: continue
            xfix.append((j, k, z, lk))
print("x* fix options", len(xfix))
lfix = []
for jp in range(9):
    for m in range(9):
        if pts[jp] in col0[R[m]] and pts[jp] != R[m]:
            lfix.append((jp, m, line_through(R[m], pts[jp])))
print("l* fix options", len(lfix))
res = []
for (j, k, z, lk) in xfix:
    sig = sig0[:]; pos = {l: p for p, l in enumerate(sig)}
    swapv(sig, z, pos[lines[j]]); pos = {l: p for p, l in enumerate(sig)}
    if lk in pos: swapv(sig, pts[k], pos[lk])
    c1 = score(sig)
    for (jp, m, lm) in lfix:
        if m == k: continue
        s2 = sig[:]; pos2 = {l: p for p, l in enumerate(s2)}
        if lm in pos2: swapv(s2, pts[m], pos2[lm])
        c2 = score(s2); res.append((c2, c1, (j, k, z, lk), (jp, m, lm)))
        wr(outp + "_%d_%d_%d.in" % (c2, j, jp), s2)
res.sort(); print("best combos", [(r[0], r[1]) for r in res[:8]])
