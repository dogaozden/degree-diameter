"""Is there an independent set of size >= T in the 477-vertex points quotient?
Clauses: at-most-one per line-clique (513 cliques covering every quotient edge), totalizer for >= T.
usage: sat2.py T SOLVER OUTPREFIX"""
import sys, time, numpy as np
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver
from pysat.formula import CNF
T = int(sys.argv[1]); solver = sys.argv[2]; outp = sys.argv[3]
E = '/home/user/degree-diameter/research/squads/polylev/r2/e08/'
n = 477
co = np.fromfile(E + 'work/cl_off.bin', dtype=np.int32); cm = np.fromfile(E + 'work/cl_mem.bin', dtype=np.int32)
clauses = []
for i in range(len(co) - 1):
    m = cm[co[i]:co[i + 1]]
    for a in range(len(m)):
        for b in range(a + 1, len(m)):
            clauses.append([-(int(m[a]) + 1), -(int(m[b]) + 1)])
card = CardEnc.atleast(lits=list(range(1, n + 1)), bound=T, top_id=n, encoding=EncType.totalizer)
t0 = time.time()
with Solver(name=solver, bootstrap_with=clauses + card.clauses) as s:
    ok = s.solve()
    print('T=%d' % T, 'SAT' if ok else 'UNSAT', 'time %.1f' % (time.time() - t0), flush=True)
    if ok:
        m = s.get_model(); sel = [v - 1 for v in m[:n] if v > 0]
        open(f'{outp}_T{T}.txt', 'w').write('\n'.join(map(str, sel)) + '\n'); print('set', len(sel), sel)
