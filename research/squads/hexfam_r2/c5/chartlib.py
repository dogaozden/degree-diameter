"""c5 helpers: affine chart of H(q) points opposite e4, isometry to e4, conversions. q prime.

Chart: point x with x0 = 1 is (1, a, b, c, c^2 - a e - b f, e, f) ~ chart vector (a, b, c, e, f).
Two chart points are opposite iff Q'(u - v) != 0, Q'(a,b,c,e,f) = c^2 - a e - b f.
Full partial ovoid = {e4} + chart set (e4 is opposite every chart point).
"""
import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/projects/hexagon-family/tools')
from q6lib import Geo, nullspace_mod

A7 = np.zeros((7, 7), dtype=np.int64)
for _i, _j in [(0, 4), (1, 5), (2, 6)]:
    A7[_i, _j] = A7[_j, _i] = 1
A7[3, 3] = -2          # B(x,y) = x^T A7 y ; B(x,x) = 2 Q(x), Q(x) = x0x4+x1x5+x2x6-x3^2


def inv(x, q):
    return pow(int(x) % q, q - 2, q)


def Q7(x, q):
    return int((x[0] * x[4] + x[1] * x[5] + x[2] * x[6] - x[3] * x[3]) % q)


def find_iso(G, pid, target, seed=1, ngen=8):
    """Matrix M (mod q) with M C[pid] proportional to C[target]. M is a product of reflections r_u(x) = x - B(x,u)/Q(u) u
    (isometries of Q), found by BFS over the point orbit of pid."""
    q = G.q
    rng = np.random.default_rng(seed)
    gens = []
    while len(gens) < ngen:
        u = rng.integers(0, q, size=7).astype(np.int64)
        Qu = Q7(u, q)
        if Qu == 0:
            continue
        gens.append((np.eye(7, dtype=np.int64) - np.outer(u, A7 @ u) * inv(Qu, q)) % q)
    M = {int(pid): np.eye(7, dtype=np.int64)}
    queue = [int(pid)]
    h = 0
    while h < len(queue):
        x = queue[h]
        h += 1
        for R in gens:
            y = (R @ G.C[x]) % q
            yid = int(G.ids_of(y[None, :])[0])
            if yid not in M:
                M[yid] = (R @ M[x]) % q
                if yid == target:
                    return M[yid]
                queue.append(yid)
    raise RuntimeError('target not reached')


def chart_of(G, M, ids):
    """chart tuples (a,b,c,e,f) of the ids after applying M; returns (list, number of ids mapped into e4^perp)."""
    q = G.q
    out, zeros = [], []
    for s in ids:
        y = (M @ G.C[int(s)]) % q
        if y[0] == 0:
            zeros.append(int(s))
            continue
        y = (y * inv(y[0], q)) % q
        out.append((int(y[1]), int(y[2]), int(y[3]), int(y[5]), int(y[6])))
    return out, zeros


def vec7(t, q):
    a, b, c, e, f = t
    return [1, a, b, c, (c * c - a * e - b * f) % q, e, f]


def ids_of_chart(G, pts):
    return [int(i) for i in G.ids_of(np.array([vec7(t, G.q) for t in pts], dtype=np.int64))]


def e4_id(G):
    return int(G.ids_of(np.array([[0, 0, 0, 0, 1, 0, 0]], dtype=np.int64))[0])


def save_set(path, ids):
    with open(path, 'w') as fh:
        fh.write(' '.join(str(int(i)) for i in ids) + '\n')
