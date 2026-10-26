"""For an incident regulus switch (mkdc2 output) make {sigma(p): p in l*} = delta(PG-line g through R_9) by swapping
sigma(p_i) with sigma(C^-1(Q_i)).  Needs C: recomputed from sigma on old points (sigma(s) = delta(C(s)) => C(s) =
delta(sigma(s))).  Tries every g through R_9; prints costs.  usage: fixl.py base.in out_prefix [newid]"""
import sys, subprocess, random
from gq import *
base, pref = sys.argv[1], sys.argv[2]; X = int(sys.argv[3]) if len(sys.argv) > 3 else n0
t = open(base).read().split(); n, dg = int(t[0]), int(t[1])
ln = [[int(x) for x in t[2+l*dg:2+l*dg+dg]] for l in range(n)]; sig = [int(x) for x in t[2+n*dg:2+n*dg+n]]
lstar = X  # line id of l* = n0 + k
pts_l = ln[lstar]; ps = [p for p in pts_l if p < n0]; x = [p for p in pts_l if p >= n0][0]
R9 = d_ln[sig[x]]                      # sigma(x*) = delta(R_9)
Cof = {}                               # C(s) for old points with sigma(s) an old line
for s in range(n0):
    if sig[s] < n0: Cof[s] = d_ln[sig[s]]
Cinv = {v: k for k, v in Cof.items()}
# PG-lines through R9
seen = set(); gl = []
for q in range(n0):
    if q == R9: continue
    g = span(PTS[R9], PTS[q])
    if g in seen: continue
    seen.add(g); gl.append(sorted(g))
rng = random.Random(1); res = []
def score(fn): 
    o = subprocess.run(["/tmp/po7", fn], env={"SCORE": "1"}, capture_output=True, text=True).stdout
    return int(o.split("cost=")[1].split()[0])
for gi, g in enumerate(gl):
    Q = [R for R in g if R != R9]
    if any(R not in Cinv for R in Q): continue
    s2 = sig[:]
    order = Q[:]; rng.shuffle(order)
    for p, R in zip(ps, order):
        a = Cinv[R]
        if a == p: continue
        s2[p], s2[a] = s2[a], s2[p]
    fn = f"{pref}_g{gi}.in"
    with open(fn, "w") as f:
        f.write(f"{n} {dg}\n")
        for l in ln: f.write(" ".join(map(str, l)) + "\n")
        for s in s2: f.write(f"{s}\n")
    c = score(fn); res.append((c, gi, "W" if is_W(g[:2]) else "h"))
res.sort(); print(res[:10], "of", len(res))
