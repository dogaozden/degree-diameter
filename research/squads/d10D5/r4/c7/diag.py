import sys; sys.argv = ['x', 'in100.sol', 'runs_diag']
sys.path.insert(0, '.')
import numpy as np, hung
from hung import *
sig = sig0.copy()
W1 = np.ones((k, N)); W2 = np.ones((k, N))
for it in range(12):
    st = state(sig)
    print('it', it, 'cost', st['cost'], 'up', int(st['up'].sum()), 'ul', int(st['ul'].sum()), 'lin_pt==1', int((st['lin_pt']==1).sum()), 'lin_pt==0', int((st['lin_pt']==0).sum()))
    S = score_matrix(sig, st, W1, W2)
    Ssub = S[np.ix_(var_pts, var_lines)]
    r, c = linear_sum_assignment(Ssub, maximize=True)
    new = sig.copy(); new[var_pts[r]] = var_lines[c]
    c2, _ = lns.cover(F, new, hubadj, listing=True)
    print('   moved', int((new != sig).sum()), 'c2', c2, 'linear obj', Ssub[r, c].sum(), 'identity obj', Ssub[np.arange(len(var_pts)), np.searchsorted(var_lines, sig[var_pts])].sum())
    W1 += st["up"]; W2 += st["ul"]
    sig = new
