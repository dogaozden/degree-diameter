import sys, time, os
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D5/r4'); sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, lns
from lns import N, PTS, LOF, PM, LM, cover, lns_step, read_sol, write_sol
S0 = read_sol(sys.argv[1]); F = S0['F']; sig = S0['sig'].copy(); hubadj = S0['hubadj']
sinv = np.empty(N, np.int64); sinv[sig] = np.arange(N)
isfree = np.zeros(N, bool); isfree[F] = True; isfreeL = np.zeros(N, bool); isfreeL[sig[F]] = True
p = F[3]; u = 69
Sset = {u}
Sset |= set(int(x) for x in np.nonzero(PM[p] & ~isfree)[0])
Sset |= set(int(sinv[M]) for M in LOF[u] if not isfreeL[M])
Sset |= set(int(sinv[w]) for w in LOF[p] if not isfreeL[w])
for w in LOF[p]:
    if isfreeL[w]: continue
    z = int(sinv[w])
    Sset |= set(int(sinv[L]) for L in LOF[z] if not isfreeL[L])
Sset = [x for x in Sset if not isfree[x]]
print('|S|', len(Sset), flush=True)
t = time.time()
new, info = lns_step(F, sig, hubadj, Sset, float(os.environ.get('STEP', 60)), 7, 1)
print('info', info, 'time %.1f' % (time.time()-t), flush=True)
if new is not None:
    c, U = cover(F, new, hubadj, listing=True)
    print('exact', c, U[:5], flush=True)
    if c == 0: write_sol(sys.argv[2] + '.sol', S0, new, 0); print('WROTE', flush=True)
