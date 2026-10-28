"""Exact test for the relaxed set problem (fact 12) on W(q): is there T, |T| >= K, with
(a) every t in T has at most one collinear neighbour in T, and (b) no two collinear points of T lie on a spread line S.
Usage: relax_sat.py Q K [solver] [sym]   sym='pt' fixes point 0 in T (only valid if Stab(S) is point-transitive; not used by default)."""
import sys, time
from itertools import combinations
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
q, K = int(sys.argv[1]), int(sys.argv[2])
sname = sys.argv[3] if len(sys.argv) > 3 else 'cadical195'
sym = sys.argv[4] if len(sys.argv) > 4 else 'none'
rd = open('W%d_lines.txt' % q).read().split('\n')
npts, nl = map(int, rd[0].split())
lines = [tuple(map(int, rd[1 + i].split())) for i in range(nl)]
S = set(map(int, open('W%d_spread.txt' % q).read().split()[1:]))
col = [set() for _ in range(npts)]
for l in lines:
    for a in l:
        for b in l:
            if a != b: col[a].add(b)
cls = []
for t in range(npts):
    for u, v in combinations(sorted(col[t]), 2):
        cls.append([-(t + 1), -(u + 1), -(v + 1)])
for i in S:
    for u, v in combinations(lines[i], 2):
        cls.append([-(u + 1), -(v + 1)])
if sym == 'pt': cls.append([1])
card = CardEnc.atleast(lits=[p + 1 for p in range(npts)], bound=K, top_id=npts + 1, encoding=EncType.seqcounter)
cls += card.clauses
t0 = time.time()
with Solver(name=sname, bootstrap_with=cls) as s:
    ok = s.solve(); dt = time.time() - t0
    if ok:
        m = s.get_model(); T = [p for p in range(npts) if m[p] > 0]
        for t in T:
            assert sum(1 for u in T if u in col[t]) <= 1
        for u, v in combinations(T, 2):
            if v in col[u]:
                assert not any(u in lines[i] and v in lines[i] for i in S)
        print('SAT relaxed q=%d K=%d %s %.1fs |T|=%d T=%s' % (q, K, sym, dt, len(T), T))
    else:
        print('UNSAT relaxed q=%d K=%d %s %.1fs' % (q, K, sym, dt))
