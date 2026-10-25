"""Single sigma swaps on the 10-flag state k10_orbit_100 (flags and hub graph fixed) that try to cover the
residual hole (65, 69): sigma(x) <-> sigma(y) with x collinear with 65 (non-freed) and sigma(y) through 69.
Scores = model holes (points + lines, with hub routes). Exhaustive over all such swaps."""
import sys, time
sys.dont_write_bytecode = True
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D5/r3/c4')
import numpy as np
from cov import N, PM, LOF, read_sol, hub_matrix, core
S = read_sol('k10_orbit_100'); F = S['F']; sig0 = S['sig']; k = len(F)
HG = hub_matrix(k, S['pairs'], S['H']); Fs = set(F)
def total(sig):
    res = core(F, sig, HG)
    return sum(int(r['unc_p'].sum()) + int(r['unc_l'].sum()) for r in res), res
base, _ = total(sig0)
print('base holes', base)
xs = [x for x in range(N) if PM[65][x] and x != 65 and x not in Fs]
ys = [int(np.where(np.array(sig0) == M)[0][0]) for M in LOF[69]]
ys = [y for y in ys if y not in Fs]
print('candidate x (collinear with 65, non-freed):', len(xs), ' candidate y (sigma(y) through 69):', ys)
best = []
t0 = time.time()
for x in xs:
    for y in ys:
        if y == x: continue
        sig = list(sig0); sig[x], sig[y] = sig[y], sig[x]
        tot, res = total(sig)
        best.append((tot, x, y, int(res[3]['unc_p'].sum()), int(res[3]['unc_l'].sum())))
best.sort()
print('time %.1fs' % (time.time() - t0), 'swaps tried', len(best))
print('best (total holes, x, y, holes of flag 65 points, holes of its line):')
for b in best[:10]: print(b)
