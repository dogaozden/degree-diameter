import sys; sys.path.insert(0, '/home/user/degree-diameter/research/squads/r1_d8c/c12')
import numpy as np
from lift import make_base, lift_edges, M
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import shortest_path
q = int(sys.argv[1]); seed = 1
N, base, match, s1, s2 = make_base(q, seed)
S = 2 * N
E = lift_edges(S, base + match)
n = M * S
A = coo_matrix((np.ones(len(E)), (E[:, 0], E[:, 1])), shape=(n, n)).tocsr()
A = A + A.T
src = np.arange(S)  # copy-0 representatives
D = shortest_path(A, method='D', unweighted=True, indices=src)
col = np.array([0] * N + [1] * N)  # colour of rep (0 point, 1 line)
for c in (0, 1):
    # same-colour vertices (any copy) at distance >6, per copy-0 rep
    rows = []
    for r in range(S):
        if col[r % S] != c: continue
        d = D[r]
        same = d[(np.arange(n) % S) == 0]  # placeholder
    # vectorised: colour of vertex id v is col[v % S]
    vc = np.tile(col, M)
    far = [int(((D[r] > 6) & (vc == c) & (np.arange(n) != r)).sum()) for r in range(S) if col[r] == c]
    far = np.array(far)
    print('colour', c, 'min far6', far.min(), 'median', np.median(far), 'max', far.max(), 'count zero', (far == 0).sum())
