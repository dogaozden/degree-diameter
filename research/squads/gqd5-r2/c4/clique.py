import numpy as np
from pysat.examples.rc2 import RC2
from pysat.formula import WCNF
import networkx as nx
import sp
from sp import COL, NP


def max_union(orbs, time_limit=None):
    """orbs: list of point lists. Returns (weight, chosen point list) maximizing total size of pairwise non-collinear orbits."""
    good = [o for o in orbs if not sp.collinear_pairs_inside(o)]
    n = len(good)
    if n == 0:
        return 0, []
    rep = np.array([o[0] for o in good])
    # conflict between orbits a,b if any collinear pair
    Mo = np.zeros((n, NP), dtype=np.int64)
    for i, o in enumerate(good):
        Mo[i, o] = 1
    C = (Mo @ COL.astype(np.int64) @ Mo.T) > 0
    np.fill_diagonal(C, False)
    w = [len(o) for o in good]
    if n <= 80:
        g = nx.Graph()
        for i in range(n):
            g.add_node(i, weight=w[i])
        for i in range(n):
            for j in range(i + 1, n):
                if not C[i, j]: g.add_edge(i, j)
        cl, wt = nx.max_weight_clique(g, weight='weight')
        ch = cl
    else:
        wcnf = WCNF()
        for i in range(n):
            for j in range(i + 1, n):
                if C[i, j]: wcnf.append([-(i + 1), -(j + 1)])
        for i in range(n):
            wcnf.append([i + 1], weight=w[i])
        with RC2(wcnf) as rc2:
            m = rc2.compute()
        ch = [i for i in range(n) if m[i] > 0]
        wt = sum(w[i] for i in ch)
    pts = sorted(p for i in ch for p in good[i])
    assert not COL[np.ix_(pts, pts)].any()
    return len(pts), pts
