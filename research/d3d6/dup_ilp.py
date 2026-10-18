"""Duplication ILP: given a bipartite graph of diameter D >= 3 and max degree <= Delta, add twins.

A twin of v gets N(v). Simultaneous twinning keeps the diameter (D >= 3): d(u',w) <= max(d(u,w),2), and for
adjacent u,v: u'-v-u-v'. Vertex w gains sum of multiplicities of its neighbours, so we maximise
sum m(u) subject to deg(w) + sum_{u ~ w} m(u) <= Delta for every w (independent ILPs per side).

python3 dup_ilp.py base q Delta [maxmult] [time]
  base: plus2 | al | pg   (the +2 core, the AL core (3 hats), or plain PG(2,q)), no filler.
"""
import json
import sys
from pathlib import Path

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import lil_matrix

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'research' / 'plus2'))
sys.path.insert(0, str(ROOT / 'problems' / 'bipartite_dd'))
import construction as C  # noqa: E402
import lib  # noqa: E402


def base_graph(base, q):
    points, lines = C.pg_plane(q)
    if base == 'pg':
        pts = [('p', p) for p in points]
        lns = [('l', j) for j in range(len(lines))]
        inc = {(('p', p), ('l', j)) for j, L in enumerate(lines) for p in L}
    else:
        A, ell, P, X = C.default_frame(points, lines)
        pts, lns, inc = C.core_incidences(points, lines, q, A, ell, P, X, hats=4 if base == 'plus2' else 3)
    n, edges, ids = C.to_graph(pts, lns, inc)
    side = [0] * len(pts) + [1] * len(lns)
    return n, edges, side


def solve_side(n, edges, side, which, Delta, maxmult, tl):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v); adj[v].append(u)
    deg = [len(a) for a in adj]
    var = [u for u in range(n) if side[u] == which and deg[u] <= Delta]
    idx = {u: i for i, u in enumerate(var)}
    rows = [w for w in range(n) if side[w] != which]
    A = lil_matrix((len(rows), len(var)))
    ub = []
    for r, w in enumerate(rows):
        for u in adj[w]:
            if u in idx:
                A[r, idx[u]] = 1
        ub.append(Delta - deg[w])
    if min(ub) < 0:
        raise ValueError('base exceeds Delta')
    res = milp(c=-np.ones(len(var)), constraints=LinearConstraint(A.tocsr(), -np.inf, np.array(ub, float)),
               integrality=np.ones(len(var)), bounds=Bounds(0, maxmult),
               options={'time_limit': tl, 'disp': True})
    m = {var[i]: int(round(x)) for i, x in enumerate(res.x) if round(x) > 0}
    bound = -res.mip_dual_bound if hasattr(res, 'mip_dual_bound') and res.mip_dual_bound is not None else None
    return m, bound, res.status


def twin(n, edges, mult):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v); adj[v].append(u)
    new = list(edges)
    k = n
    for u, c in sorted(mult.items()):
        for _ in range(c):
            new += [(min(k, w), max(k, w)) for w in adj[u]]
            k += 1
    return k, new


def main():
    base, q, Delta = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    maxmult = int(sys.argv[4]) if len(sys.argv) > 4 else 2
    tl = float(sys.argv[5]) if len(sys.argv) > 5 else 300
    n, edges, side = base_graph(base, q)
    print(f'{base} q={q}: n={n} maxdeg={lib.max_degree(n, edges)} Delta={Delta}', flush=True)
    mult = {}
    for which in (0, 1):
        m, bound, st = solve_side(n, edges, side, which, Delta, maxmult, tl)
        print(f'  side {which}: {sum(m.values())} twins (bound {bound}, status {st})', flush=True)
        mult.update(m)
    N, E = twin(n, edges, mult)
    ok = lib.is_valid(N, E, Delta, 3)
    print(f'  total n={N} valid={ok}', flush=True)
    if ok:
        out = HERE / 'graphs' / f'dup_{base}_q{q}_d{Delta}_n{N}.json'
        out.write_text(json.dumps({'case': f'd{Delta}D3', 'value': N, 'output': [N, E]}))
        print('  wrote', out)


if __name__ == '__main__':
    main()
