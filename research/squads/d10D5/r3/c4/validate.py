import sys, time
sys.dont_write_bytecode = True
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D5/r3/c4')
import numpy as np
import cov
from cov import N, PM, LM, read_sol, hub_matrix, core, bfs_all, dists

name = sys.argv[1]; full = len(sys.argv) > 2 and sys.argv[2] == 'full'
S = read_sol(name); F = S['F']; sig = S['sig']; k = len(F)
HG = hub_matrix(k, S['pairs'], S['H'])
t0 = time.time()
res = core(F, sig, HG)
adj, nv = bfs_all(F, sig, S['mv0'], S['mv1'], S['nu'], S['pairs'], S['H'])
print(name, 'k', k, 'hub pairs', len(S['pairs']), 'vertices', nv, 'built in %.1fs' % (time.time() - t0))
sources = [6 * p for p in F] + [6 * (N + int(sig[p])) for p in F]
if full: sources = [6 * v for v in range(2 * N)] + [v for v in range(6 * 2 * N, nv)]
total_fail = 0; fails_by_src = {}
t0 = time.time()
Fset = set(F)
for s in sources:
    d = dists(adj, s)
    f = sum(1 for t in range(nv) if t != s and (d[t] < 0 or d[t] > 5))
    total_fail += f
    fails_by_src[s] = d
print('BFS over', len(sources), 'sources in %.1fs' % (time.time() - t0), '| total failing (source,target) pairs:', total_fail)
print('%-4s %-5s %-5s | %5s %5s %5s %5s | %5s %5s | BFS-coset1 pts-fail  model-holes  match' % ('i', 'p', 'l', 'cap_i', 'cap_ii', 'cap_iii', 'Oo_cov', 'unc_p', 'unc_l'))
for i, r in enumerate(res):
    p = r['p']; l = r['l']
    d = fails_by_src[6 * p]
    bfs_pts = np.zeros(N, bool)
    for u in range(N):
        if any(d[6 * u + h] < 0 or d[6 * u + h] > 5 for h in (1, 4)): bfs_pts[u] = True
    dl = fails_by_src[6 * (N + l)]
    bfs_ln = np.zeros(N, bool)
    for m in range(N):
        if any(dl[6 * (N + m) + h] < 0 or dl[6 * (N + m) + h] > 5 for h in (2, 5)): bfs_ln[m] = True
    nonF = np.array([x not in Fset for x in range(N)])
    mp = r['unc_p'] & nonF
    bp = bfs_pts & ~PM[p] & nonF
    ml = r['unc_l'] & np.array([m not in set(sig[x] for x in F) for m in range(N)])
    bl = bfs_ln & ~LM[l] & np.array([m not in set(sig[x] for x in F) for m in range(N)])
    print('%-4d %-5d %-5d | %5d %5d %5d %5d | %5d %5d | pts: bfs %3d model %3d  diff %3d | lines: bfs %3d model %3d diff %3d' % (
        i, p, l, r['cap_i'], r['cap_ii'], r['cap_iii'], r['ncov_p'], int(mp.sum()), int(ml.sum()),
        int(bp.sum()), int(mp.sum()), int(np.count_nonzero(bp ^ mp)), int(bl.sum()), int(ml.sum()), int(np.count_nonzero(bl ^ ml))))
