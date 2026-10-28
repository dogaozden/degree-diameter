"""3-level test bed: types H,H,D over GQ G (points/lines of one GQ).
L0 (H): A=points, B=lines.  L1 (H): A=points, B=lines.  L2 (D): A=lines, B=points.
Transitions: 0->1 M01: points(L0) -> lines(L1) (bijection, non-friendly, no freed set).
             1->2 identity on points, freed set R (points of L1 whose matching edge to L2 is deleted).
             2->0 identity on lines: lines(L2) -> lines(L0) (friendly, no freed set).
Vertex id: level j, element e (0..np-1 points, np..np+nl-1 lines) -> j*per + e.  Hubs after 3*per.
"""
import sys, os, random
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
import numpy as np
from gqlib import Q4, W
from levels import write_edges

_cache = {}
def getG(q, kind='Q4'):
    key = (q, kind)
    if key not in _cache:
        _cache[key] = Q4(q) if kind == 'Q4' else W(q)
    return _cache[key]

def base_edges(G, M01, R):
    """M01: array len np (point -> line index). R: iterable of freed point ids. returns n_base, edges, per"""
    np_, nl = G.np, G.nl
    per = np_ + nl
    E = []
    for j in range(3):
        b = j * per
        for l, pts in enumerate(G.lines):
            for p in pts:
                E.append((b + p, b + np_ + l))
    # 0 -> 1 : L0 point p - L1 line M01[p]
    for p in range(np_):
        E.append((0 * per + p, 1 * per + np_ + int(M01[p])))
    # 1 -> 2 : L1 point x - L2 point x for x not freed
    Rs = set(R)
    for x in range(np_):
        if x not in Rs:
            E.append((1 * per + x, 2 * per + x))
    # 2 -> 0 : L2 line l - L0 line l
    for l in range(nl):
        E.append((2 * per + np_ + l, 0 * per + np_ + l))
    return 3 * per, E, per

def random_M01(G, seed):
    rng = random.Random(seed)
    p = list(range(G.nl)); rng.shuffle(p)
    return np.array(p)

def diam_numpy(n, E):
    """all-pairs BFS via boolean matrix products; returns (diameter or None if disconnected, max degree)."""
    A = np.zeros((n, n), dtype=bool)
    for a, b in E:
        A[a, b] = A[b, a] = True
    deg = A.sum(1).max()
    reach = np.eye(n, dtype=bool)
    frontier = reach.copy()
    dist = 0
    Af = A.astype(np.float32)
    while True:
        nxt = (frontier.astype(np.float32) @ Af) > 0
        new = nxt & ~reach
        if not new.any():
            break
        dist += 1
        reach |= new
        frontier = new
    if not reach.all():
        return None, int(deg)
    return dist, int(deg)

def write(path, n, E):
    write_edges(path, n, E)
