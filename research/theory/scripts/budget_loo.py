"""DATA_CHECK.md §3: leave-one-out for the one-parameter budget model, with and without the group excess factor."""
import math, numpy as np
import data_check2 as dc
from data_check import records
rows = records(); BB = sorted([r for r in rows if r['best'] and r['D'] >= 7], key=lambda r: (r['D'], r['d']))
def err(r, lb, exf): return math.log(r['N'] / dc.N_solve(r['d'], r['D'], lambda m: dc.mu_max_budget(m, r['D'], math.exp(lb)), exf(r)))
for lab, exf in (('with group excess', dc.excess), ('generic mu only', lambda r: 1.0)):
    grid = np.linspace(0, math.log(1e7), 281)
    sse = [sum(err(r, lb, exf) ** 2 for r in BB) for lb in grid]; lb = grid[int(np.argmin(sse))]
    e = np.array([err(r, lb, exf) for r in BB]); loo = []
    for i in range(len(BB)):
        g2 = np.linspace(lb - 2, lb + 2, 81)
        l2 = g2[int(np.argmin([sum(err(r, x, exf) ** 2 for j, r in enumerate(BB) if j != i) for x in g2]))]
        loo.append(err(BB[i], l2, exf))
    loo = np.array(loo)
    print('%-18s B=%.0f s  rms %.3f  max %.3f  LOO rms %.3f  per-D mean: %s' % (lab, math.exp(lb), math.sqrt((e ** 2).mean()), abs(e).max(),
          math.sqrt((loo ** 2).mean()), ' '.join('D%d %+.3f' % (D, np.mean([x for x, r in zip(e, BB) if r['D'] == D])) for D in (7, 8, 9, 10))))
