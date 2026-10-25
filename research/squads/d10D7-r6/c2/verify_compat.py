# brute-force check of orbit_graph compatibility and self-compatibility (independent of subgeo.orbit_graph)
import numpy as np, sys
import groups as g
from common import V, Bval, N
from subgeo import orbits, orbit_graph
def brute(perms):
    lab = orbits(perms); no = lab.max() + 1
    members = [np.nonzero(lab == o)[0] for o in range(no)]
    sc = []
    for m in members:
        X = V[m]; Bm = Bval(X[:, None, :], X[None, :, :]) != 0
        ok = all(Bm[i, j] for i in range(len(m)) for j in range(len(m)) if i != j)
        sc.append(ok)
    S = [o for o in range(no) if sc[o]]
    A = np.zeros((len(S), len(S)), bool)
    for a, oa in enumerate(S):
        for b, ob in enumerate(S):
            if a == b: continue
            X = V[members[oa]]; Y = V[members[ob]]
            A[a, b] = bool((Bval(X[:, None, :], Y[None, :, :]) != 0).all())
    return no, S, A, members
name = sys.argv[1]
G = g.groups_def()
perms = [x if isinstance(x, np.ndarray) and x.shape == (N,) else g.perm_from_matrix(x) for x in G[name]]
no, S, Ab, members = brute(perms)
lab = orbits(perms); sizes, mem2, S2, A2 = orbit_graph(lab)
print('orbits', no, 'selfcompat brute', len(S), 'selfcompat fast', len(S2), 'same set', sorted(S) == sorted(S2.tolist()))
# compare A on common index order (both sorted by orbit label)
idx = {o: i for i, o in enumerate(S2.tolist())}
ok = True
for a, oa in enumerate(S):
    for b, ob in enumerate(S):
        if a != b and Ab[a, b] != A2[idx[oa], idx[ob]]: ok = False
print('compat matrices agree:', ok, ' brute edges', int(Ab.sum() // 2), 'fast edges', int(A2.sum() // 2))
