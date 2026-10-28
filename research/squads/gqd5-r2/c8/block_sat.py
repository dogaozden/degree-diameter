"""Smallest blocking set of W(q) w.r.t. lines: point set meeting every line (hitting set of the 156 lines).
Usage: block_sat.py Q K [solver] [mode]; asks for a set of size <= K (mode 'atmost') ; K-1 UNSAT gives a lower bound.
Symmetry (mode 'sym'): PSp(4,q) is point-transitive, so for a nonempty blocking set WLOG point 0 is in it."""
import sys, time
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
q, K = int(sys.argv[1]), int(sys.argv[2])
sname = sys.argv[3] if len(sys.argv) > 3 else 'cadical195'
mode = sys.argv[4] if len(sys.argv) > 4 else 'plain'
rd = open('W%d_lines.txt' % q).read().split('\n')
npts, nl = map(int, rd[0].split())
lines = [list(map(int, rd[1 + i].split())) for i in range(nl)]
cls = [[p + 1 for p in l] for l in lines]
if mode == 'sym':     # point-transitivity of PSp(4,q): WLOG point 0 is in the blocking set
    cls.append([1])
card = CardEnc.atmost(lits=[p + 1 for p in range(npts)], bound=K, top_id=npts + 1, encoding=EncType.seqcounter)
cls += card.clauses
t0 = time.time()
with Solver(name=sname, bootstrap_with=cls) as s:
    ok = s.solve(); dt = time.time() - t0
    if ok:
        m = s.get_model(); B = [p for p in range(npts) if m[p] > 0]
        assert all(any(p in B for p in l) for l in lines)
        print('SAT q=%d K=%d %s %.1fs blocking set size %d: %s' % (q, K, mode, dt, len(B), B))
    else:
        print('UNSAT q=%d K=%d %s %.1fs : no blocking set of size <= %d' % (q, K, mode, dt, K))
