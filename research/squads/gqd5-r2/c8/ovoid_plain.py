"""Independent cross-check of ovoid_sat.py with weaker symmetry: mode 'none' = no symmetry breaking,
mode 'pt' = only point-transitivity (x_0 = 1). Usage: ovoid_plain.py Q K SOLVER MODE"""
import sys, time
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
q, K, sname, mode = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4]
rd = open('W%d_lines.txt' % q).read().split('\n')
npts, nl = map(int, rd[0].split())
lines = [list(map(int, rd[1 + i].split())) for i in range(nl)]
cls = []
for l in lines:   # at most one point of every line (partial ovoid of W(q) = meets every line at most once)
    for a in range(len(l)):
        for b in range(a + 1, len(l)):
            cls.append([-(l[a] + 1), -(l[b] + 1)])
if mode == 'pt': cls.append([1])
card = CardEnc.atleast(lits=[p + 1 for p in range(npts)], bound=K, top_id=npts + 1, encoding=EncType.seqcounter)
cls += card.clauses
t0 = time.time()
with Solver(name=sname, bootstrap_with=cls) as s:
    ok = s.solve(); dt = time.time() - t0
    if ok:
        m = s.get_model(); S = [p for p in range(npts) if m[p] > 0]
        assert all(sum(1 for p in S if p in l) <= 1 for l in lines)
        print('SAT q=%d K=%d solver=%s mode=%s %.1fs size %d' % (q, K, sname, mode, dt, len(S)))
    else:
        print('UNSAT q=%d K=%d solver=%s mode=%s %.1fs' % (q, K, sname, mode, dt))
