# Exact maximum dual segment set at q=2 by MaxSAT (RC2). Constraint: for L in G and points p != r on L, not (M through p in G and K through r in G), M,K != L.
import sys, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/conics2-r1/c7')
from common import *
from pysat.formula import WCNF
from pysat.examples.rc2 import RC2
q = int(sys.argv[1])
q, N, LPa, PLa, X = load(f'{D}/data/hex_q{q}.bin')
LP = LPa.tolist(); PL = PLa.tolist()
w = WCNF()
seen = set()
for L in range(N):
    w.append([L + 1], weight=1)
    pts = LP[L]
    for i in range(len(pts)):
        for j in range(len(pts)):
            if i == j: continue
            p, r = pts[i], pts[j]
            for M in PL[p]:
                if M == L: continue
                for K in PL[r]:
                    if K == L or K == M: continue
                    cl = tuple(sorted({-(L+1), -(M+1), -(K+1)}))
                    if cl not in seen:
                        seen.add(cl); w.append(list(cl))
print('N', N, 'hard clauses', len(seen), flush=True)
t = time.time()
rc2 = RC2(w, solver='g4')
model = rc2.compute()
G = [i for i in range(N) if model[i] > 0]
print('q', q, 'max dual segment set size (exact)', len(G), 'time', round(time.time() - t, 1), flush=True)
print('valid', valid(LPa, PLa, N, np.array(G)))
open(f'/home/user/degree-diameter/research/squads/conics2-r1/c7/exact_q{q}_G.txt', 'w').write(' '.join(map(str, G)))
