"""Is there an independent set of size T in a quotient graph (CSR prefix)? SAT via pysat (cardinality totalizer)."""
import sys, time, numpy as np
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver
prefix, T = sys.argv[1], int(sys.argv[2])
n = int(np.fromfile(prefix + '_n.bin', dtype=np.int32)[0])
off = np.fromfile(prefix + '_off.bin', dtype=np.int32)
nb = np.fromfile(prefix + '_nb.bin', dtype=np.int32)
clauses = []
for v in range(n):
    for u in nb[off[v]:off[v + 1]]:
        if u > v: clauses.append([-(v + 1), -(int(u) + 1)])
card = CardEnc.atleast(lits=list(range(1, n + 1)), bound=T, top_id=n, encoding=EncType.seqcounter)
t0 = time.time()
with Solver(name='cadical153', bootstrap_with=clauses + card.clauses) as s:
    ok = s.solve()
    print(prefix, 'T=%d' % T, 'SAT' if ok else 'UNSAT', 'time %.1f' % (time.time() - t0), flush=True)
    if ok:
        m = s.get_model()
        sel = [v - 1 for v in m[:n] if v > 0]
        open(f'{prefix}_sat{T}.txt', 'w').write('\n'.join(map(str, sel)) + '\n')
        print('set size', len(sel))
