"""Degree q+2+k, diameter 4: P(W(q),x) + point copies (weights w) + line copies that may use point copies as
stand-ins.

Rules (proof in REPORT.md, "stand-ins"): every line L gets sum_{p in L} w(p) <= k+2 new neighbours (point copies);
a line copy y_L takes, for each p in L, one stand-in: p itself or one of its w(p) copies; each stand-in serves at
most k line copies. So the line multiset M needs: every point p on at most k(1 + w(p)) entries of M.
Order q^3 + (q+2)q^2 + sum(w) + |M|.

python3 as_share.py ilp q k SECONDS [lock_w2]   joint ILP (HiGHS) for w and M; lock_w2=1 forces w >= Q_1 + Q_2
python3 as_share.py build q k SOLUTION.json     builds the graph, checks with lib.is_valid, writes graphs/
"""
import json
import sys
import time
from collections import Counter
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from as_gq import build, check_gq, incidence_edges, lib  # noqa: E402
from as_w2 import weighted_2ovoid  # noqa: E402


def ilp(q, k, secs, lock_w2):
    from scipy.optimize import Bounds, LinearConstraint, milp
    from scipy.sparse import lil_matrix
    F, pts, lines = build(q)
    n, m = len(pts), len(lines)
    # variables: w_0..w_{n-1}, then m_0..m_{m-1}
    A = lil_matrix((m + n, n + m))
    for j, L in enumerate(lines):
        for p in L:
            A[j, p] = 1                 # line cap: sum w <= k+2
            A[m + p, n + j] = 1         # point cap: sum m_L - k w_p <= k
    for p in range(n):
        A[m + p, p] = -k
    lo = np.full(m + n, -np.inf)
    hi = np.concatenate([np.full(m, k + 2), np.full(n, k)])
    lb = np.zeros(n + m)
    ub = np.concatenate([np.full(n, k + 2), np.full(m, k)])
    if lock_w2:
        W2, _, _ = weighted_2ovoid(F, pts)
        for p, w in W2.items():
            lb[p] = w
    t0 = time.time()
    res = milp(-np.ones(n + m), constraints=[LinearConstraint(A.tocsr(), lo, hi)], integrality=np.ones(n + m),
               bounds=Bounds(lb, ub), options={'time_limit': secs, 'disp': False})
    out = {'q': q, 'k': k, 'status': res.status, 'message': res.message, 'seconds': time.time() - t0,
           'bound': getattr(res, 'mip_dual_bound', None)}
    if res.x is not None:
        x = np.round(res.x).astype(int)
        out['w'] = {int(p): int(x[p]) for p in range(n) if x[p]}
        out['M'] = [int(j) for j in range(m) for _ in range(x[n + j])]
        out['extra'] = int(x.sum())
        out['order'] = n + m + out['extra']
    print({a: b for a, b in out.items() if a not in ('w', 'M')})
    path = HERE / 'runs' / f'share_q{q}_k{k}_lock{lock_w2}.json'
    path.write_text(json.dumps(out))
    print('wrote', path)


def build_graph(q, k, sol):
    F, pts, lines = build(q)
    check_gq(q, pts, lines)
    n0 = len(pts)
    W = Counter({int(p): w for p, w in sol['w'].items()})
    M = sol['M']
    assert all(sum(W[p] for p in L) <= k + 2 for L in lines)
    on = [[] for _ in range(n0)]
    for j, L in enumerate(lines):
        for p in L:
            on[p].append(n0 + j)
    edges = incidence_edges(n0, lines)
    v = n0 + len(lines)
    copies = {}
    for p, w in sorted(W.items()):
        copies[p] = []
        for _ in range(w):
            edges += [(v, Lv) for Lv in on[p]]
            copies[p].append(v)
            v += 1
    used = Counter()        # stand-in vertex -> number of line copies it serves
    for j in M:
        y = v
        v += 1
        for p in lines[j]:
            s = min([p] + copies.get(p, []), key=lambda u: used[u])
            assert used[s] < k, f'no free stand-in for point {p}'
            used[s] += 1
            edges.append((s, y))
    n = v
    ok = lib.is_valid(n, edges, q + 2 + k, 4)
    print(f'q={q} k={k}: |W|={sum(W.values())}, |M|={len(M)}, n={n}, max degree {lib.max_degree(n, edges)}, '
          f'is_valid = {ok}')
    if ok:
        out = HERE / 'graphs' / f'as_share_q{q}_k{k}_n{n}.json'
        out.write_text(json.dumps({'case': f'd{q+2+k}D4', 'value': n, 'output': [n, [list(e) for e in edges]]}))
        print('wrote', out)


if __name__ == '__main__':
    if sys.argv[1] == 'ilp':
        ilp(int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4]), int(sys.argv[5]) if len(sys.argv) > 5 else 0)
    else:
        build_graph(int(sys.argv[2]), int(sys.argv[3]), json.loads(Path(sys.argv[4]).read_text()))
