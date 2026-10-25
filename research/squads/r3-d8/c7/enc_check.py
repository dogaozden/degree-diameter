import sys, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r3-d8/c7')
import g_sat, gh
from pysat.solvers import Cadical153
q, j, M = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
use_sum = sys.argv[4] == 'sum'
prof = sys.argv[5]
H = gh.load(q); N = H.N
t0 = time.time()
cls, pool = g_sat.encode(H, j, M, use_sum, prof, sym=False)
print('encoded', len(cls), 'clauses', pool.top, 'vars', round(time.time()-t0,2), 's', flush=True)
# fix the constant labelling t = c, l = c (c given as argv[6])
c = int(sys.argv[6])
assum = []
for x in range(N):
    assum.append(1 + x * M + c)
for y in range(N):
    assum.append(1 + (N + y) * M + c)
s = Cadical153(bootstrap_with=cls)
t0 = time.time()
r = s.solve(assumptions=assum)
print('constant labelling c=%d sum=%s: %s in %.2fs' % (c, use_sum, r, time.time()-t0), flush=True)
