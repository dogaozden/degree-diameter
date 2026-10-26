"""Exact test: does W(q) have a partial ovoid (pairwise non-collinear point set) of size >= K?
Symmetry: PSp(4,q) is point-transitive and transitive on opposite pairs, so WLOG the set contains points 0 and P1
(P1 = the first point non-collinear with 0). Usage: ovoid_sat.py Q K [solver] [timeout_s]"""
import sys, time, itertools
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
q, K = int(sys.argv[1]), int(sys.argv[2])
solver_name = sys.argv[3] if len(sys.argv) > 3 else 'cadical195'
rd = open('W%d_col.txt' % q).read().split('\n')
n = int(rd[0]); col = [set(map(int, rd[1 + p].split()[1:])) for p in range(n)]
P1 = min(p for p in range(1, n) if p not in col[0])
forced_out = col[0] | col[P1] | {0, P1}
cand = [p for p in range(n) if p not in forced_out]
var = lambda p: p + 1
cls = []
for p in range(n):
    for r in col[p]:
        if p < r: cls.append([-var(p), -var(r)])
cls.append([var(0)]); cls.append([var(P1)])
for p in forced_out - {0, P1}: cls.append([-var(p)])
card = CardEnc.atleast(lits=[var(p) for p in range(n)], bound=K, top_id=n + 1, encoding=EncType.seqcounter)
cls += card.clauses
t0 = time.time()
with Solver(name=solver_name, bootstrap_with=cls) as s:
    ok = s.solve()
    dt = time.time() - t0
    if ok:
        m = s.get_model(); S = [p for p in range(n) if m[p] > 0]
        print('SAT q=%d K=%d time %.1fs set %s' % (q, K, dt, S))
        assert all(r not in col[p] for p in S for r in S if p != r)
    else:
        print('UNSAT q=%d K=%d time %.1fs (no partial ovoid of size >= %d, containing 0 and P1)' % (q, K, dt, K))
