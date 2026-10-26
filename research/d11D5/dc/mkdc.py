"""Regulus switch on W(8) with sigma = delta o C, C a collineation with C(L_i) in W (the switch lines) and p_i chosen with
C^-1(delta(p_i)) in W.  Adds K switches far apart.  usage: mkdc.py K seed out.in"""
import sys, random
from gq import *
K, seed, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
rng = random.Random(seed)
def find_C(Ls, tries=200000):
    for t in range(tries):
        M = randmat(rng); Cp = pmap(M)
        ok = all(is_W([Cp[p] for p in LINES[L][:2]]) for L in Ls[:3])
        if not ok: continue
        if not all(is_W([Cp[p] for p in LINES[L][:2]]) for L in Ls): continue
        nW = sum(is_W([Cp[p] for p in l[:2]]) for l in LINES)
        if nW == n0: continue   # symplectic: skip
        return M, Cp, nW
    return None
# first C from the first switch, then the other switches must also satisfy C(L_i) in W: choose their h with delta(R_i)
# mapped into W by C -- i.e. search h among hyperbolic lines.
def hyperbolic_lines():
    seen = set()
    while True:
        a, b = rng.sample(range(n0), 2)
        if Bf(PTS[a], PTS[b]) == 0: continue
        h = span(PTS[a], PTS[b])
        if h in seen: continue
        seen.add(h); yield sorted(h)
gen = hyperbolic_lines()
used_pts = set(); used_lines = set(); switches = []
C = None
col = [set() for _ in range(n0)]
for l in LINES:
    for a in l: col[a].update(l)
def lines_of_h(h): return [d_pt[R] for R in h]
while C is None:
    h = next(gen); Ls = lines_of_h(h)
    r = find_C(Ls, 20000)
    if r: M, Cp, nW = r; C = Cp; print("C found, W-lines preserved", nW, file=sys.stderr)
Minv = matinv(M); Cinv = pmap(Minv)
def choose_p(L):
    good = []
    for p in LINES[L]:
        img = [Cinv[q] for q in LINES[d_pt[p]]]
        if is_W(img[:2]): good.append(p)
    return good
def try_switch(Ls):
    if any(l in used_lines for l in Ls): return None
    ps = []
    for L in Ls:
        g = [p for p in choose_p(L) if p not in used_pts and all(p not in col[q] for q in ps)]
        if not g: return None
        ps.append(rng.choice(g))
    return ps
first = True
while len(switches) < K:
    if not first:
        h = next(gen); Ls = lines_of_h(h)
        if not all(is_W([C[p] for p in LINES[L][:2]]) for L in Ls): continue
    first = False
    # keep away from earlier switches
    near = set()
    for (Ls0, ps0) in switches:
        for L in Ls0: near.update(LINES[L])
        near.update(ps0)
    if any(set(LINES[L]) & near for L in Ls): continue
    ps = try_switch(Ls)
    if ps is None: continue
    switches.append((Ls, ps)); used_lines.update(Ls); used_pts.update(ps)
    print("switch", len(switches), "lines", Ls, "points", ps, file=sys.stderr)
n = n0 + K
L2 = [list(l) for l in LINES]
for k, (Ls, ps) in enumerate(switches):
    X = n0 + k
    for L, p in zip(Ls, ps): L2[L] = [X if q == p else q for q in L2[L]]
    L2.append(list(ps))
sig = [d_pt[C[p]] for p in range(n0)] + [n0 + k for k in range(K)]
with open(out, "w") as f:
    f.write(f"{n} 9\n")
    for l in L2: f.write(" ".join(map(str, l)) + "\n")
    for s in sig: f.write(f"{s}\n")
