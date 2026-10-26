import sys
sys.dont_write_bytecode = True
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D5/r3/c4')
import numpy as np
from cov import N, PM, LM, LOF, read_sol, hub_matrix, core
for name in ['k9_valid', 'k10_orbit_100', 'k10_orbit_38']:
    S = read_sol(name); F = S['F']; sig = S['sig']; k = len(F)
    HG = hub_matrix(k, S['pairs'], S['H'])
    Ls = [sig[p] for p in F]
    kap = [sum(1 for j, f in enumerate(F) if j != i and PM[p][f]) for i, p in enumerate(F)]
    conc = [sum(1 for j, m in enumerate(Ls) if j != i and LM[Ls[i]][m]) for i in range(k)]
    for label, H_ in (('no hub routes', None), ('with hub routes', HG)):
        res = core(F, sig, H_)
        print(f'{name} k={k} {label}: collinear freed pairs={sum(kap)//2} concurrent freed-line pairs={sum(conc)//2}')
        print('  flag  p    kappa  conc  cap_i  cap_ii cap_iii  pts_covered(of 343-freed)  point_holes  line_holes')
        for i, r in enumerate(res):
            print('  %2d  %4d  %4d  %4d  %5d  %5d  %5d  %5d  %5d  %5d' % (i, F[i], kap[i], conc[i], r['cap_i'], r['cap_ii'],
                  r['cap_iii'], r['ncov_p'], int(r['unc_p'].sum()), int(r['unc_l'].sum())))
        print('  total point holes', sum(int(r['unc_p'].sum()) for r in res), ' total line holes', sum(int(r['unc_l'].sum()) for r in res))
