#!/usr/bin/env python3
"""Card c6 sanity check for q=3: an ovoid of H(3) is a perfect code of the collinearity graph (each closed
collinearity neighbourhood, 1 + q(q+1) = 13 points, holds exactly one ovoid point; 364/13 = 28 = q^3+1).
Found by SAT; its (q+1)*28 = 112 pencil lines are scored with tools/dualseg_check.py. usage: ovoid3c.py OUTFILE"""
import sys, time, itertools
sys.path.insert(0, '/home/user/degree-diameter/research/squads/conics2-r1/tools')
from hexload import load
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver
out = sys.argv[1]
q, N, LP, PL, X = load('/home/user/degree-diameter/research/squads/conics2-r1/data/hex_q3.bin')
nbr = []
for p in range(N):
    s = {p}
    for l in PL[p]:
        s |= set(int(x) for x in LP[l])
    nbr.append(sorted(s))
top = N
cl = []
for p in range(N):
    enc = CardEnc.equals(lits=[x + 1 for x in nbr[p]], bound=1, top_id=top, encoding=EncType.seqcounter)
    top = max(top, enc.nv)
    cl += enc.clauses
t0 = time.time()
with Solver(name='cadical153', bootstrap_with=cl) as S:
    ok = S.solve()
    print('perfect-code SAT' if ok else 'UNSAT', f'{time.time()-t0:.1f}s', flush=True)
    if ok:
        m = S.get_model()
        O = [p for p in range(N) if m[p] > 0]
        G = sorted(set(int(l) for p in O for l in PL[p]))
        print('O', len(O), 'G', len(G), flush=True)
        open(out, 'w').write('\n'.join(map(str, G)) + '\n')
