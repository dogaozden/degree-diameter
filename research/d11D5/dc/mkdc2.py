"""Incident regulus switch with sigma = delta o C.  h = hyperbolic PG-line R_1..R_9; switch lines L_i = delta(R_i), i <= 8;
C with C(L_i) in W; p_i in L_i with C^-1(delta(p_i)) in W (if possible); x* on L_1..L_8 and on l* = {p_1..p_8, x*};
sigma = delta o C on old points, except sigma(C^-1(R_9)) = l*, sigma(x*) = delta(R_9).
usage: mkdc2.py seed out.in [KS]  (KS switches sharing one C: later h are taken in the plane delta(axis)^perp)"""
import sys, random
from gq import *
seed, out = int(sys.argv[1]), sys.argv[2]; KS = int(sys.argv[3]) if len(sys.argv) > 3 else 1
rng = random.Random(seed)
col = [set() for _ in range(n0)]
for l in LINES:
    for a in l: col[a].update(l)
def rand_h(pool=None):
    while True:
        a, b = rng.sample(pool if pool else range(n0), 2)
        if Bf(PTS[a], PTS[b]): return sorted(span(PTS[a], PTS[b]))
h = rand_h(); Ls = [d_pt[R] for R in h]
while True:
    M = randmat(rng); C = pmap(M)
    if not all(is_W([C[p] for p in LINES[L][:2]]) for L in Ls[:3]): continue
    pres = [li for li, l in enumerate(LINES) if is_W([C[p] for p in l[:2]])]
    if len(pres) < n0: break
Cinv = pmap(matinv(M))
axis = [li for li in range(n0) if all(set(LINES[li]) & set(LINES[m]) or li == m for m in pres)]
print("preserved", len(pres), "axis", axis, file=sys.stderr)
P0 = d_ln[axis[0]]   # delta(axis), a point; later h lie in P0^perp
plane = [p for p in range(n0) if Bf(PTS[p], PTS[P0]) == 0 and p != P0]
sw = []; usedL = set(); usedP = set(); omitted = []
def build(h):
    perm = list(range(9)); rng.shuffle(perm)
    for om in perm:
        Ls = [d_pt[h[i]] for i in range(9) if i != om]
        if any(L in usedL for L in Ls): continue
        ps = []
        for L in Ls:
            good = [p for p in LINES[L] if is_W([Cinv[q] for q in LINES[d_pt[p]][:2]]) and p not in usedP and all(p not in col[q] for q in ps)]
            if not good: good = [p for p in LINES[L] if p not in usedP and all(p not in col[q] for q in ps)]
            if not good: break
            ps.append(rng.choice(good))
        if len(ps) == 8: return Ls, ps, h[om]
    return None
r = build(h); sw.append(r); usedL.update(r[0]); usedP.update(r[1])
for k in range(1, KS):
    for t in range(2000):
        h2 = rand_h(plane)
        if sum(d_pt[R] in usedL for R in h2) > k: continue
        r = build(h2)
        if r: sw.append(r); usedL.update(r[0]); usedP.update(r[1]); break
    else: print("no second switch", file=sys.stderr); sys.exit(1)
n = n0 + len(sw)
L2 = [list(l) for l in LINES]; sig = [d_pt[C[p]] for p in range(n0)]
for k, (Ls, ps, R9) in enumerate(sw):
    X = n0 + k
    for L, p in zip(Ls, ps): L2[L] = [X if q == p else q for q in L2[L]]
    L2.append(list(ps) + [X])
    s9 = Cinv[R9]; assert sig[s9] == d_pt[R9]
    sig[s9] = n0 + k; sig.append(d_pt[R9])
    print("switch", k, "lines", Ls, "points", ps, "R9", R9, file=sys.stderr)
assert sorted(sig) == list(range(n))
with open(out, "w") as f:
    f.write(f"{n} 9\n")
    for l in L2: f.write(" ".join(map(str, l)) + "\n")
    for s in sig: f.write(f"{s}\n")
