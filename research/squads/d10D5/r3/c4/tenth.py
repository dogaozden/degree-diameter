"""Try 10th freed flags (p, l) with l through the uncovered point 69 (hole of flag 65 in k10_orbit_100).
sigma changes by the swap sigma(p) := l (old preimage x of l takes sigma_old(p)); the hub graph gets the
edge (point-side hub of flag 65) -- (line-side hub of the new flag). Scores = model holes (points+lines)."""
import sys, time
sys.dont_write_bytecode = True
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D5/r3/c4')
import numpy as np
from cov import N, PM, LM, LOF, LINES, read_sol, hub_matrix, core
S = read_sol('k10_orbit_100')
F0 = S['F'][:9]; sig0 = S['sig']
HG9 = hub_matrix(9, [(a, b) for a, b in S['pairs'] if a // 2 < 9 and b // 2 < 9], 2)
hole_pt = 69; anchor = 3
def total(F, sig, HG):
    res = core(F, sig, HG)
    return sum(int(r['unc_p'].sum()) + int(r['unc_l'].sum()) for r in res), res
rows = []
t0 = time.time()
for l in LOF[hole_pt]:
    for p in LINES[l]:
        if p in F0 or p == hole_pt: continue
        x = sig0.index(l)
        if x in F0: continue
        sig = list(sig0); sig[x] = sig0[p]; sig[p] = l
        assert sorted(sig) == list(range(N))
        F = F0 + [p]
        HG = np.zeros((10, 10), bool); HG[:9, :9] = HG9; HG[anchor, 9] = True
        kap = sum(1 for f in F0 if PM[p][f])
        conc = sum(1 for m in [sig0[f] for f in F0] if LM[l][m])
        tot, res = total(F, sig, HG)
        tot0, _ = total(F, sig, None)
        rows.append((tot, tot0, p, l, kap, conc, int(res[-1]['unc_p'].sum()), int(res[-1]['unc_l'].sum())))
rows.sort()
print('candidates', len(rows), 'time %.1fs' % (time.time() - t0))
print('holes(with new hub edge), holes(no hub routes), new point p, new line l, kappa(p), concurrent freed lines, holes of p, holes of l')
for r in rows[:12]: print(r)
