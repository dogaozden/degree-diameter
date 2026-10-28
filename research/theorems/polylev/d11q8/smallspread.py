"""smallspread.py: does Q(6,q) have a line spread (a partition of its points into totally singular lines)?
Exact cover of the points by all t.s. lines, SAT (CaDiCaL). Usage: python3 smallspread.py HEXBIN SECONDS"""
import sys
sys.path.insert(0, '..')
import numpy as np
from hexlib import Hex
from g2 import gram_row
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

H = Hex(sys.argv[1]); q, N = H.q, H.N
X = H.coord
G = np.array([gram_row(H, X[p]) for p in range(N)])          # b(p, .) as a row vector
B = np.zeros((N, N), dtype=np.int64)
for j in range(7):
    B = H.ADD[B, H.MUL[G[:, j][:, None], X[:, j][None, :]]]
lines = set()
for p in range(N):
    for x in np.where(B[p] == 0)[0]:
        if x <= p:
            continue
        lam = np.arange(1, q)
        pts = set(H.point_ids(H.ADD[X[x][None, :], H.MUL[lam[:, None], X[p][None, :]]]).tolist()) | {p, int(x)}
        lines.add(tuple(sorted(pts)))
lines = sorted(lines)
print(f'q={q}: {len(lines)} t.s. lines', flush=True)
on = [[] for _ in range(N)]
for i, l in enumerate(lines):
    for p in l:
        on[p].append(i + 1)
pool = IDPool(start_from=len(lines) + 1); S = Cadical153()
for p in range(N):
    for cl in CardEnc.equals(lits=on[p], bound=1, vpool=pool, encoding=EncType.seqcounter).clauses:
        S.add_clause([int(v) for v in cl])
res = S.solve()
print('line spread:', 'EXISTS' if res else 'NONE (UNSAT)', flush=True)
if res:
    m = S.get_model(); sp = [lines[i] for i in range(len(lines)) if m[i] > 0]
    hexset = set(tuple(sorted(r.tolist())) for r in H.lines)
    print(f'{len(sp)} lines, of which {sum(l in hexset for l in sp)} are hexagon lines')
