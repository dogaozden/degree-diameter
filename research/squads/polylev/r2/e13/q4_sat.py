"""q=4: non-pencil 4-dominating 5-sets of lines (SAT). Variables x_M (lines). Constraints: every line L has a chosen
line in Ball4(L); at most 5 chosen; no pencil: for each point z, not all 5 lines through z are chosen; line 0 chosen
(WLOG by transitivity of G2(4) on lines). Writes the first few solutions with blocking clauses."""
import sys, time
import numpy as np
from pysat.solvers import Cadical195
from pysat.card import CardEnc, EncType
from common import *
q = 4
H = load(q)
B = ball_matrix_cached(H, q)
Lc = H.L
M0 = int(sys.argv[1]) if len(sys.argv) > 1 else 0
nsol = int(sys.argv[2]) if len(sys.argv) > 2 else 5
top = Lc
clauses = []
for L in range(Lc):
    clauses.append([int(m) + 1 for m in np.nonzero(B[L])[0]])
card = CardEnc.atmost(lits=[m + 1 for m in range(Lc)], bound=q + 1, top_id=Lc, encoding=EncType.seqcounter)
top = max(top, card.nv)
s = Cadical195(bootstrap_with=clauses + card.clauses)
for z in range(H.N):
    s.add_clause([-(int(m) + 1) for m in H.PL[z]])   # not all lines through z chosen
s.add_clause([M0 + 1])
sols = []
t = time.time()
while len(sols) < nsol and s.solve():
    m = s.get_model()
    S = sorted(v - 1 for v in m if 0 < v <= Lc and v - 1 < Lc and v > 0 and (v - 1) < Lc and m[v - 1] > 0)
    S = [l for l in range(Lc) if m[l] > 0]
    sols.append(S)
    print('solution', len(sols), S, 'size', len(S), 'time', round(time.time() - t, 1), flush=True)
    s.add_clause([-(l + 1) for l in S])  # block this set
    # block only supersets-free: this exact set
np.save(f'q4_nonpencil_sat_M{M0}.npy', np.array(sols, dtype=np.int64))
print('pairwise distances of first solution (1 = within 4):')
if sols:
    S = sols[0]
    print(np.array([[int(B[a, b]) for b in S] for a in S]))
